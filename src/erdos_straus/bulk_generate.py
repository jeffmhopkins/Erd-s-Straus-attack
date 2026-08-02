#!/usr/bin/env python3
"""Bulk generation of explicit Erdős–Straus certificates for hard primes.

This is an optimized, dependency-light re-implementation of the residual
method used in :mod:`erdos_straus.residual_solver`, written for scale
(it drives the full 10^11 run: 128,671,219 hard primes). Three output
formats via --store: ``full`` (explicit R,a,b,c records), ``rmap``
(compact minimal-R map), and ``rseq`` (streaming uint8 R-sequence with
sha256-pinned metadata: ``{prefix}.rvals.u8.gz`` + ``.meta.json`` +
``.tail.json``, the format of the 10^11 dataset).

Key differences from ``residual_solver.solve_residual``:

* Integer-only factoring by trial division (no sympy per-call overhead).
  Because the target ``n`` is a known prime and ``a = (n+R)/4 < n``, the
  factorization of ``m^2 = (n*a)^2`` is ``{n: 2}`` combined with the squared
  factorization of ``a`` — and ``a`` is small enough (< n/4) to factor by
  trial division against a precomputed prime table almost instantly.
* Divisors are generated directly from that factorization and scanned for one
  lying in the required residue class ``k ≡ -m (mod R)``.
* Hard primes are produced with a fast numpy sieve and the search is
  parallelized across CPU cores.

For a hard prime ``n ≡ 1 (mod 4)`` (all six hard residues mod 840 are
``≡ 1 mod 4``), the admissible residuals are ``R ≡ 3 (mod 4)``:
``R = 3, 7, 11, 15, ...``. We return the certificate for the *minimal* such
``R``.

Run as a script::

    python -m erdos_straus.bulk_generate --max 120000000 \
        --out data/hard_primes_1.2e8_solutions.json.gz
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from typing import Dict, List, Optional, Tuple

HARD_RESIDUES = frozenset({1, 121, 169, 289, 361, 529})

# Precomputed small primes for trial division of a = (n+R)/4 < n/4 + 100.
# Correct full factorization needs primes up to sqrt(a): for n up to 1e11,
# a <= ~2.5e10 and sqrt(a) < 158_200. The 180000 default covers n up to
# ~1.29e11; raise the bound before pushing past that.
_SMALL_PRIMES: List[int] = []


def _init_small_primes(bound: int = 180000) -> None:
    global _SMALL_PRIMES
    if _SMALL_PRIMES and _SMALL_PRIMES[-1] >= bound:
        return
    sieve = bytearray([1]) * (bound + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(bound ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    _SMALL_PRIMES = [i for i in range(2, bound + 1) if sieve[i]]


def factorize(a: int) -> Dict[int, int]:
    """Full prime factorization of ``a`` by trial division.

    Assumes ``a`` is small enough that its largest prime factor's square
    either divides out or leaves a prime remainder within the small-prime
    table's reach (true for a < ~(max small prime)^2).
    """
    factors: Dict[int, int] = {}
    n = a
    for p in _SMALL_PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            factors[p] = e
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def _divisors(factors: Dict[int, int]) -> List[int]:
    divs = [1]
    for p, e in factors.items():
        pk = 1
        powers = []
        for _ in range(e + 1):
            powers.append(pk)
            pk *= p
        divs = [d * w for d in divs for w in powers]
    return divs


def solve_residual(n: int, R: int, a_factors: Optional[Dict[int, int]] = None
                   ) -> Optional[Tuple[int, int, int]]:
    """Try to solve 4/n = 1/a+1/b+1/c with a = (n+R)/4 for the given R.

    Returns the certificate ``(a, b, c)`` with ``a < b <= c`` on success,
    else ``None``. ``a_factors`` may be passed to reuse a factorization.
    """
    if R <= 0 or (n + R) % 4 != 0:
        return None
    a = (n + R) // 4
    if a <= 0:
        return None
    m = n * a

    if a_factors is None:
        a_factors = factorize(a)
    # m^2 = n^2 * a^2  (n prime, n does not divide a since a < n)
    m2_factors = {p: 2 * e for p, e in a_factors.items()}
    m2_factors[n] = m2_factors.get(n, 0) + 2

    want = (-m) % R
    best_k = None
    for k in _divisors(m2_factors):
        if k % R == want:
            if best_k is None or k < best_k:
                best_k = k
    if best_k is None:
        return None

    k = best_k
    if (k + m) % R != 0:
        return None
    other = (n * n) * (a * a) // k  # m^2 // k, exact
    if (other + m) % R != 0:
        return None
    b = (k + m) // R
    c = (other + m) // R
    if b <= 0 or c <= 0:
        return None
    if b > c:
        b, c = c, b
    # Final exact check.
    if 4 * a * b * c != n * (b * c + a * c + a * b):
        return None
    return (a, b, c)


def minimal_certificate(n: int, max_R: int = 400
                        ) -> Optional[Tuple[int, int, int, int]]:
    """Return (a, b, c, R) for the minimal admissible R, or None."""
    # n ≡ 1 (mod 4) for hard primes -> R ≡ 3 (mod 4).
    start = (4 - (n % 4)) % 4
    if start == 0:
        start = 4
    for R in range(start, max_R + 1, 4):
        sol = solve_residual(n, R)
        if sol is not None:
            return (*sol, R)
    return None


# --- sieving ---------------------------------------------------------------

def _require_numpy():
    try:
        import numpy as np  # noqa: F401
        return np
    except ImportError as exc:  # pragma: no cover
        raise ImportError(
            "bulk_generate needs numpy for sieving; install with "
            "`pip install -e \".[gen]\"` or `pip install numpy`."
        ) from exc


def _base_primes(bound: int) -> List[int]:
    """Simple sieve returning all primes <= bound (bytearray, low memory)."""
    sieve = bytearray([1]) * (bound + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(bound ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(range(i * i, bound + 1, i)))
    return [i for i in range(2, bound + 1) if sieve[i]]


def hard_primes_upto(limit: int) -> List[int]:
    """All primes p <= limit with p mod 840 in the hard residue set.

    Monolithic numpy sieve — simplest, but allocates one bool per integer
    (~1 GB at 10^9). Prefer :func:`hard_primes_upto_segmented` at large scale.
    """
    np = _require_numpy()
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    primes = np.nonzero(sieve)[0]
    residues = primes % 840
    mask = np.isin(residues, np.array(sorted(HARD_RESIDUES)))
    return primes[mask].tolist()


def hard_primes_upto_segmented(limit: int, segment_size: int = 1 << 23,
                               progress: bool = False,
                               as_array: bool = False):
    """All hard-residue primes p <= limit via a segmented sieve.

    Memory is bounded by the base-prime table (primes up to sqrt(limit)) plus
    one bool array of ``segment_size``. Returns a Python list by default;
    pass ``as_array=True`` for a numpy int64 array (8 bytes/prime — required
    at 1e11 scale, where a list would need ~4 GB).
    """
    np = _require_numpy()
    hard_res = np.array(sorted(HARD_RESIDUES))
    base = _base_primes(int(math.isqrt(limit)) + 1)

    parts = []
    lo = 2
    n_seg = (limit - 1) // segment_size + 1
    seg_idx = 0
    while lo <= limit:
        hi = min(lo + segment_size - 1, limit)
        seg = np.ones(hi - lo + 1, dtype=bool)
        # Cross off multiples of each base prime within [lo, hi].
        for p in base:
            if p * p > hi:
                break
            start = max(p * p, ((lo + p - 1) // p) * p)
            seg[start - lo::p] = False
        idx = np.nonzero(seg)[0]
        primes = idx + lo
        if primes.size:
            res = primes % 840
            mask = np.isin(res, hard_res)
            if mask.any():
                parts.append(primes[mask].astype(np.int64))
        seg_idx += 1
        if progress and (seg_idx % 200 == 0 or hi == limit):
            n_found = sum(len(a) for a in parts)
            print(f"[sieve] segment {seg_idx}/{n_seg} "
                  f"(up to {hi:,}), {n_found:,} hard so far", flush=True)
        lo = hi + 1
    arr = np.concatenate(parts) if parts else np.empty(0, dtype=np.int64)
    return arr if as_array else arr.tolist()


# --- parallel driver -------------------------------------------------------

def _worker(chunk: List[int]) -> List[Tuple[int, int, int, int, int]]:
    _init_small_primes()
    out = []
    for n in chunk:
        res = minimal_certificate(n)
        if res is None:
            out.append((n, -1, -1, -1, -1))  # sentinel: unsolved
        else:
            a, b, c, R = res
            out.append((n, R, a, b, c))
    return out


def generate(limit: int, out_path: str, workers: Optional[int] = None,
             progress: bool = True, segmented: bool = False,
             store: str = "full") -> Dict[str, object]:
    """Generate certificates for all hard primes <= limit.

    ``store="full"`` writes ``{n: {R,a,b,c}}``; ``store="rmap"`` writes the
    compact minimal-R map ``{n: R}`` (explicit triples reconstruct
    deterministically from (n, R) and are re-derived during verification).
    ``segmented=True`` uses the low-memory segmented sieve (required at 10^9).
    """
    if store not in ("full", "rmap"):
        raise ValueError("store must be 'full' or 'rmap'")
    _init_small_primes()
    t0 = time.time()
    if progress:
        print(f"[sieve] hard primes up to {limit:,} "
              f"({'segmented' if segmented else 'monolithic'}) ...", flush=True)
    if segmented:
        primes = hard_primes_upto_segmented(limit, progress=progress)
    else:
        primes = hard_primes_upto(limit)
    if progress:
        print(f"[sieve] {len(primes):,} hard primes "
              f"({time.time() - t0:.1f}s)", flush=True)

    workers = workers or os.cpu_count() or 1
    # Chunk for multiprocessing.
    n_chunks = workers * 8 if len(primes) > workers * 8 else 1
    chunk_size = (len(primes) + n_chunks - 1) // n_chunks
    chunks = [primes[i:i + chunk_size] for i in range(0, len(primes), chunk_size)]

    results: List[Tuple[int, int, int, int, int]] = []
    t1 = time.time()
    if workers > 1 and len(primes) > 1000:
        from multiprocessing import Pool
        done = 0
        with Pool(workers) as pool:
            for part in pool.imap_unordered(_worker, chunks):
                results.extend(part)
                done += len(part)
                if progress:
                    print(f"[solve] {done:,}/{len(primes):,} "
                          f"({time.time() - t1:.1f}s)", flush=True)
    else:
        results = _worker(primes)

    results.sort(key=lambda r: r[0])

    solutions: Dict[str, object] = {}
    unsolved: List[int] = []
    R_counter: Dict[int, int] = {}
    max_R = 0
    max_R_prime = 0
    for n, R, a, b, c in results:
        if R == -1:
            unsolved.append(n)
            continue
        if store == "rmap":
            solutions[str(n)] = R
        else:
            solutions[str(n)] = {"R": R, "a": a, "b": b, "c": c}
        R_counter[R] = R_counter.get(R, 0) + 1
        if R > max_R:
            max_R = R
            max_R_prime = n

    if out_path.endswith(".gz"):
        import gzip
        with gzip.open(out_path, "wt", compresslevel=9) as f:
            json.dump(solutions, f, separators=(",", ":"))
    else:
        with open(out_path, "w") as f:
            json.dump(solutions, f, separators=(",", ":"))

    stats = {
        "limit": limit,
        "num_hard_primes": len(primes),
        "num_solved": len(solutions),
        "num_unsolved": len(unsolved),
        "unsolved_sample": unsolved[:50],
        "max_R": max_R,
        "max_R_prime": max_R_prime,
        "R_distribution": dict(sorted(R_counter.items())),
        "elapsed_sec": round(time.time() - t0, 1),
        "out_path": out_path,
    }
    if progress:
        print(f"[done] solved {len(solutions):,}/{len(primes):,}, "
              f"max R={max_R} at n={max_R_prime}, "
              f"{stats['elapsed_sec']}s", flush=True)
        if unsolved:
            print(f"[warn] {len(unsolved)} unsolved (max_R too small?): "
                  f"{unsolved[:10]}", flush=True)
    return stats


def _worker_rseq(chunk) -> Tuple[object, List[Tuple[int, int, int, int, int]]]:
    """Solve a numpy chunk of primes; return (uint8 R-array, tail entries).

    Tail entries (R >= 43, or sentinel R = -1 for unsolved) carry the full
    verified triple so the repo can store them explicitly.
    """
    import numpy as np
    _init_small_primes()
    out = np.empty(len(chunk), dtype=np.uint8)
    tail = []
    for i, n in enumerate(chunk.tolist()):
        res = minimal_certificate(n)
        if res is None:
            out[i] = 0
            tail.append((n, -1, 0, 0, 0))
        else:
            a, b, c, R = res
            out[i] = R if R <= 255 else 255
            if R >= 43:
                tail.append((n, R, a, b, c))
    return out, tail


def generate_rseq(limit: int, out_prefix: str,
                  workers: Optional[int] = None,
                  scratch_npz: Optional[str] = None,
                  progress: bool = True) -> Dict[str, object]:
    """Large-scale generation with compact R-sequence output.

    Writes three artifacts:
      {out_prefix}.rvals.u8.gz  - gzip of the uint8 minimal-R values, in
                                  ascending-prime order (primes regenerate
                                  deterministically by the segmented sieve;
                                  sha256 of the prime bytes is recorded)
      {out_prefix}.meta.json    - limit, count, hashes, distribution, record
      {out_prefix}.tail.json    - explicit verified triples for R >= 43
    plus, if scratch_npz is given, a full (primes, rvals) npz for direct
    verification without re-sieving.
    """
    import gzip
    import hashlib
    import numpy as np

    _init_small_primes()
    t0 = time.time()
    if progress:
        print(f"[sieve] hard primes up to {limit:,} (segmented, array) ...",
              flush=True)
    primes = hard_primes_upto_segmented(limit, segment_size=1 << 25,
                                        progress=progress, as_array=True)
    total = len(primes)
    sieve_secs = round(time.time() - t0, 1)
    if progress:
        print(f"[sieve] {total:,} hard primes ({sieve_secs}s)", flush=True)

    workers = workers or os.cpu_count() or 1
    n_chunks = max(1, min(512, total // 200_000 + 1))
    bounds = [total * i // n_chunks for i in range(n_chunks + 1)]
    chunks = [primes[bounds[i]:bounds[i + 1]] for i in range(n_chunks)]

    rvals = np.empty(total, dtype=np.uint8)
    tail: List[Tuple[int, int, int, int, int]] = []
    t1 = time.time()
    pos = 0
    from multiprocessing import Pool
    with Pool(workers) as pool:
        for ci, (out, t) in enumerate(pool.imap(_worker_rseq, chunks)):
            rvals[pos:pos + len(out)] = out
            pos += len(out)
            tail.extend(t)
            if progress and (ci % 8 == 0 or ci == n_chunks - 1):
                el = time.time() - t1
                eta = el / max(pos, 1) * (total - pos)
                print(f"[solve] {pos:,}/{total:,} ({el:.0f}s, "
                      f"ETA {eta/60:.0f}m)", flush=True)

    unsolved = [e[0] for e in tail if e[1] == -1]
    dist_counts = np.bincount(rvals, minlength=256)
    R_distribution = {int(R): int(c) for R, c in enumerate(dist_counts)
                      if c > 0 and R > 0}
    solved_tail = [e for e in tail if e[1] > 0]
    max_R = max((e[1] for e in solved_tail), default=int(max(
        (R for R in R_distribution), default=0)))
    if solved_tail and max_R >= 43:
        max_R_prime = min(e[0] for e in solved_tail if e[1] == max_R)
    else:
        max_R_prime = 0

    raw = rvals.tobytes()
    with gzip.open(out_prefix + ".rvals.u8.gz", "wb", compresslevel=9) as f:
        f.write(raw)
    tail_json = [{"p": e[0], "R": e[1], "a": e[2], "b": e[3], "c": e[4]}
                 for e in solved_tail]
    with open(out_prefix + ".tail.json", "w") as f:
        json.dump(tail_json, f, indent=1)
    stats = {
        "limit": limit,
        "num_hard_primes": total,
        "num_unsolved": len(unsolved),
        "unsolved_sample": unsolved[:50],
        "max_R": int(max_R),
        "max_R_prime": int(max_R_prime),
        "R_distribution": R_distribution,
        "first_prime": int(primes[0]) if total else None,
        "last_prime": int(primes[-1]) if total else None,
        "sha256_rvals": hashlib.sha256(raw).hexdigest(),
        "sha256_primes": hashlib.sha256(primes.tobytes()).hexdigest(),
        "sieve_secs": sieve_secs,
        "elapsed_secs": round(time.time() - t0, 1),
        "format": "uint8 minimal-R values in ascending-prime order; primes "
                  "regenerate via hard_primes_upto_segmented(limit)",
    }
    with open(out_prefix + ".meta.json", "w") as f:
        json.dump(stats, f, indent=2)
    if scratch_npz:
        np.savez_compressed(scratch_npz, primes=primes, rvals=rvals)
    if progress:
        print(f"[done] {total - len(unsolved):,}/{total:,} solved, "
              f"max R={max_R} at n={max_R_prime}, "
              f"{stats['elapsed_secs']}s", flush=True)
    return stats


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max", type=int, default=120_000_000,
                    help="upper bound on n (inclusive)")
    ap.add_argument("--out", type=str,
                    default="data/hard_primes_1.2e8_solutions.json.gz",
                    help="output path; gzip-compressed when it ends in .gz")
    ap.add_argument("--workers", type=int, default=None)
    ap.add_argument("--segmented", action="store_true",
                    help="use the low-memory segmented sieve (needed at 10^9)")
    ap.add_argument("--store", choices=["full", "rmap", "rseq"], default="full",
                    help="'full' writes {n:{R,a,b,c}}; 'rmap' writes compact "
                         "{n:R}; 'rseq' writes the uint8 R-sequence format "
                         "(--out is then a path prefix)")
    ap.add_argument("--scratch-npz", type=str, default=None,
                    help="rseq only: also save a full (primes, rvals) npz "
                         "for direct verification")
    ap.add_argument("--stats-out", type=str, default=None,
                    help="optional path to write JSON run statistics")
    args = ap.parse_args(argv)

    if args.store == "rseq":
        stats = generate_rseq(args.max, args.out, workers=args.workers,
                              scratch_npz=args.scratch_npz)
    else:
        stats = generate(args.max, args.out, workers=args.workers,
                         segmented=args.segmented, store=args.store)
    if args.stats_out:
        with open(args.stats_out, "w") as f:
            json.dump(stats, f, indent=2)
    print(json.dumps({k: v for k, v in stats.items()
                      if k != "unsolved_sample"}, indent=2))
    return 0 if stats["num_unsolved"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
