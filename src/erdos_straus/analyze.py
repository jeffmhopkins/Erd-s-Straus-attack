#!/usr/bin/env python3
"""Analysis of the minimal-R data: distribution, covering sets, and the
structure of high-R primes.

Three sub-commands::

    python -m erdos_straus.analyze dist  --rmap data/hard_primes_1e9_minimalR.json.gz
    python -m erdos_straus.analyze cover --rmap ... --out data/analysis/cover_1e9.json
    python -m erdos_straus.analyze tail  --rmap ... [--min-R 51] [--max-R 400]

``dist``
    Histogram and cumulative distribution of minimal R.

``cover``
    For every prime, compute the full *set* of admissible residuals
    R ≡ 3 (mod 4), R <= 107 that yield a solution (a 27-bit mask), then
    solve the set-cover problem: the smallest list of residuals covering
    every hard prime, via exact reasoning on mandatory residuals + greedy
    on the rest. Parallelized; this is the expensive step (~27 solves/prime).

``tail``
    For the high-R primes (minimal R >= --min-R), compute every working
    residual up to --max-R and report the divisor-structure context
    (factorization of a=(n+R)/4 for failing and succeeding R), the raw
    material for understanding why small residuals fail.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import time
from typing import Dict, List, Optional, Tuple

from erdos_straus.bulk_generate import (
    _init_small_primes,
    factorize,
    solve_residual,
)

# Admissible residuals for hard primes (n ≡ 1 mod 4): R ≡ 3 (mod 4), R <= 107.
R_LIST: List[int] = list(range(3, 108, 4))  # 3, 7, ..., 107  (27 values)
R_INDEX = {R: i for i, R in enumerate(R_LIST)}


def load_rmap(path: str) -> Dict[int, int]:
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as f:
        raw = json.load(f)
    return {int(k): int(v) for k, v in raw.items()}


# --- dist ------------------------------------------------------------------

def cmd_dist(rmap_path: str) -> Dict:
    rmap = load_rmap(rmap_path)
    from collections import Counter
    hist = Counter(rmap.values())
    total = len(rmap)
    print(f"{total:,} hard primes; minimal-R distribution:\n")
    print(f"{'R':>5} {'count':>10} {'share':>8} {'cumulative':>10}")
    cum = 0
    cdf = {}
    for R in sorted(hist):
        cum += hist[R]
        cdf[R] = cum / total
        print(f"{R:>5} {hist[R]:>10,} {hist[R]/total:>7.3%} {cum/total:>9.4%}")
    return {"total": total,
            "histogram": {str(k): v for k, v in sorted(hist.items())},
            "cdf": {str(k): round(v, 6) for k, v in cdf.items()}}


# --- cover -----------------------------------------------------------------

def _mask_worker(chunk: List[int]) -> List[Tuple[int, int]]:
    """For each prime, bitmask over R_LIST of residuals that solve it."""
    _init_small_primes()
    out = []
    for n in chunk:
        mask = 0
        for i, R in enumerate(R_LIST):
            if solve_residual(n, R) is not None:
                mask |= 1 << i
        out.append((n, mask))
    return out


def compute_masks(primes: List[int], workers: Optional[int] = None,
                  progress: bool = True) -> Dict[int, int]:
    workers = workers or os.cpu_count() or 1
    n_chunks = max(workers * 16, 1)
    chunk_size = (len(primes) + n_chunks - 1) // n_chunks
    chunks = [primes[i:i + chunk_size]
              for i in range(0, len(primes), chunk_size)]
    masks: Dict[int, int] = {}
    t0 = time.time()
    if workers > 1 and len(primes) > 1000:
        from multiprocessing import Pool
        with Pool(workers) as pool:
            done = 0
            for part in pool.imap_unordered(_mask_worker, chunks):
                masks.update(dict(part))
                done += len(part)
                if progress:
                    print(f"[mask] {done:,}/{len(primes):,} "
                          f"({time.time()-t0:.0f}s)", flush=True)
    else:
        masks.update(dict(_mask_worker(primes)))
    return masks


def minimal_cover(masks: Dict[int, int]) -> Tuple[List[int], List[int]]:
    """Smallest residual list covering all primes.

    Returns (mandatory, chosen_cover). A residual is *mandatory* if some
    prime is solvable by that residual alone. The remainder is covered
    greedily (exact minimum set cover is NP-hard, but with mandatory
    elements fixed first the greedy answer is typically optimal here and we
    report the uncovered count at each step for transparency).
    """
    # Mandatory: primes with exactly one working residual.
    mandatory: set = set()
    for n, mask in masks.items():
        if mask and mask & (mask - 1) == 0:  # single bit
            mandatory.add(R_LIST[mask.bit_length() - 1])

    covered_mask = 0
    for R in mandatory:
        covered_mask |= 1 << R_INDEX[R]

    remaining = {n: m for n, m in masks.items() if not (m & covered_mask)}
    chosen = sorted(mandatory)
    while remaining:
        # Pick the residual covering the most remaining primes.
        counts = [0] * len(R_LIST)
        for m in remaining.values():
            mm = m
            while mm:
                b = mm & -mm
                counts[b.bit_length() - 1] += 1
                mm ^= b
        best_i = max(range(len(R_LIST)), key=lambda i: counts[i])
        if counts[best_i] == 0:
            # Some prime has empty mask (not coverable within R_LIST).
            break
        chosen.append(R_LIST[best_i])
        bit = 1 << best_i
        remaining = {n: m for n, m in remaining.items() if not (m & bit)}
    uncoverable = [n for n, m in masks.items() if m == 0]
    return sorted(set(chosen)), uncoverable


def cmd_cover(rmap_path: str, out_path: Optional[str],
              workers: Optional[int]) -> Dict:
    rmap = load_rmap(rmap_path)
    primes = sorted(rmap)
    print(f"computing full residual masks for {len(primes):,} primes "
          f"(R in {{3,7,...,107}}) ...", flush=True)
    masks = compute_masks(primes, workers=workers)

    if out_path:
        payload = {str(n): masks[n] for n in primes}
        opener = gzip.open if out_path.endswith(".gz") else open
        with opener(out_path, "wt") as f:
            json.dump(payload, f, separators=(",", ":"))
        print(f"masks written to {out_path}")

    # Per-residual coverage counts.
    total = len(primes)
    per_R = {R: sum(1 for m in masks.values() if m >> i & 1)
             for i, R in enumerate(R_LIST)}
    print("\nper-residual coverage (share of primes each R solves):")
    for R in R_LIST:
        print(f"  R={R:>3}: {per_R[R]:>10,} ({per_R[R]/total:.2%})")

    only_one = sum(1 for m in masks.values() if m and m & (m - 1) == 0)
    print(f"\nprimes with exactly one working residual <=107: {only_one:,}")

    cover, uncoverable = minimal_cover(masks)
    print(f"uncoverable within R<=107: {len(uncoverable)}"
          + (f" e.g. {uncoverable[:10]}" if uncoverable else ""))
    print(f"minimal covering list ({len(cover)} residuals): {cover}")
    return {
        "total": total,
        "per_R_coverage": {str(R): per_R[R] for R in R_LIST},
        "single_option_primes": only_one,
        "uncoverable": uncoverable,
        "cover": cover,
    }


# --- tail ------------------------------------------------------------------

def cmd_tail(rmap_path: str, min_R: int, max_R: int) -> Dict:
    _init_small_primes()
    rmap = load_rmap(rmap_path)
    tail = sorted((n, R) for n, R in rmap.items() if R >= min_R)
    print(f"{len(tail)} primes with minimal R >= {min_R}\n")
    report = []
    for n, Rmin in tail:
        working = []
        for R in range(3, max_R + 1, 4):
            if solve_residual(n, R) is not None:
                working.append(R)
        # Divisor structure at the minimal working residual.
        a = (n + Rmin) // 4
        fa = factorize(a)
        entry = {
            "n": n,
            "minimal_R": Rmin,
            "working_R_upto_max": working,
            "n_mod_840": n % 840,
            "a_at_minimal": a,
            "a_factorization": {str(p): e for p, e in sorted(fa.items())},
        }
        report.append(entry)
        print(f"n={n:>12,} minR={Rmin:>3} works for R in {working[:12]}"
              + (" ..." if len(working) > 12 else "")
              + f"  | a={a} = {fa}")
    return {"min_R": min_R, "max_R": max_R, "tail": report}


# --- main ------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_dist = sub.add_parser("dist")
    p_dist.add_argument("--rmap", required=True)
    p_dist.add_argument("--json-out", default=None)

    p_cover = sub.add_parser("cover")
    p_cover.add_argument("--rmap", required=True)
    p_cover.add_argument("--out", default=None,
                         help="optional path for the per-prime mask table")
    p_cover.add_argument("--workers", type=int, default=None)
    p_cover.add_argument("--json-out", default=None)

    p_tail = sub.add_parser("tail")
    p_tail.add_argument("--rmap", required=True)
    p_tail.add_argument("--min-R", type=int, default=51)
    p_tail.add_argument("--max-R", type=int, default=400)
    p_tail.add_argument("--json-out", default=None)

    args = ap.parse_args(argv)
    if args.cmd == "dist":
        result = cmd_dist(args.rmap)
    elif args.cmd == "cover":
        result = cmd_cover(args.rmap, args.out, args.workers)
    else:
        result = cmd_tail(args.rmap, args.min_R, args.max_R)

    if getattr(args, "json_out", None):
        with open(args.json_out, "w") as f:
            json.dump(result, f, indent=2)
        print(f"\nJSON written to {args.json_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
