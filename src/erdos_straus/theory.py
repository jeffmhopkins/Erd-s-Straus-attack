#!/usr/bin/env python3
"""Theoretical machinery for the residual method: obstruction theory,
failure classification, and the growth model for the minimal residual.

Mathematical setup
------------------
For a hard prime p (p ≡ 1 mod 4) and admissible residual R ≡ 3 (mod 4):
a = (p+R)/4, m = pa, and a certificate is a divisor k | m² with
k ≡ -m (mod R).  Since 4a ≡ p (mod R):

    m ≡ 4⁻¹ p²  (mod R)   — a SQUARE modulo every prime r | R.

Hence, for every prime r | R with r ≡ 3 (mod 4)  (at least one exists):

    (−m | r) = (−1 | r) = −1  — the target class is a NON-residue mod r.

Every divisor of m² is a product of prime factors of m, so:

**Proposition 1 (character obstruction).** If for some prime r | R with
r ≡ 3 (mod 4) every prime factor q of m = pa satisfies (q | r) = +1, then
residual R fails at p.  [All divisors of m² are QRs mod r; the target is not.]

**Theorem 2 (exact criterion for R = 3).**  For p ≡ 1 (mod 4), 3 ∤ p:
residual 3 succeeds  ⟺  (p+3)/4 has a prime factor ≡ 2 (mod 3).
[Mod 3 the unit group has order 2, so character = class; k = q works.]

**Proposition 3 (guaranteed-success classes).** Let t = −4⁻¹p² mod R.
If a has a prime factor q with q ≡ t·p^{-i} (mod R) for some i ∈ {0,1,2},
then k = q·pⁱ is a certificate — success.  Note t·p⁻² ≡ −4⁻¹ (mod R)
independent of p.  Contrapositive: failure ⟹ a has no prime factor in the
(≤3) classes S_R(p) = {t, tp⁻¹, tp⁻²} — a sieve condition of dimension
κ_R = |S_R(p)|/φ(R) on the linear form (p+R)/4.

Failure taxonomy (per failing pair (p, R)):
  Type I  — character obstruction of Prop. 1 holds (unavoidable failure).
  Type II — some prime factor of m is a non-residue mod every relevant r,
            yet no divisor lands in the exact class (a "class miss").

This module computationally validates Prop 1 / Thm 2 / Prop 3 against the
residual-mask dataset, classifies failures, analyzes the four critical
primes, fits the decay of per-R failure rates, and runs the independence
model that predicts the growth of the record minimal R.
"""

from __future__ import annotations

import argparse
import gzip
import json
import math
import os
import time
from collections import Counter, defaultdict
from typing import Dict, List, Optional, Sequence, Tuple

from erdos_straus.bulk_generate import _init_small_primes, factorize
from erdos_straus.analyze import R_LIST, R_INDEX, load_rmap


# --- basic number theory ---------------------------------------------------

def jacobi(a: int, n: int) -> int:
    """Jacobi symbol (a|n) for odd n > 0."""
    assert n > 0 and n % 2 == 1
    a %= n
    result = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def prime_factors_of_R(R: int) -> List[int]:
    return sorted(factorize(R).keys())


def obstruction_primes_of_R(R: int) -> List[int]:
    """Prime factors r | R with r ≡ 3 (mod 4) — the carriers of Prop. 1."""
    return [r for r in prime_factors_of_R(R) if r % 4 == 3]


# --- failure classification ------------------------------------------------

def classify_failure(p: int, R: int) -> Dict:
    """Classify a failing pair (p, R) as Type I or Type II.

    Returns a dict with the obstruction prime (if Type I), the factor
    classes, and Prop-3 data. Assumes (p, R) genuinely fails.
    """
    a = (p + R) // 4
    fa = factorize(a)
    qs = sorted(set(fa.keys()) | {p})
    obs = obstruction_primes_of_R(R)
    type1_r = None
    for r in obs:
        if all(jacobi(q, r) == 1 for q in qs):
            type1_r = r
            break
    # Prop 3 classes (sanity: none of a's factors may lie in them).
    t = (-pow(4, -1, R) * p * p) % R
    pinv = pow(p, -1, R)
    S = {t % R, (t * pinv) % R, (t * pinv * pinv) % R}
    hit = sorted(q for q in fa if (q % R) in S)
    return {
        "p": p, "R": R,
        "type": "I" if type1_r is not None else "II",
        "obstruction_prime": type1_r,
        "a": a,
        "a_factors": {str(q): e for q, e in sorted(fa.items())},
        "factor_jacobi": {
            str(q): {str(r): jacobi(q, r) for r in obs} for q in qs
        },
        "prop3_classes": sorted(S),
        "prop3_violations": hit,  # must be empty for a genuine failure
    }


# --- Theorem 2 validation (exact R=3 criterion) ----------------------------

def _r3_worker(chunk: List[Tuple[int, int]]) -> Tuple[int, int, List[int]]:
    """chunk of (p, bit) where bit = 1 if R=3 works per the mask data.
    Returns (n_checked, n_agree, disagreements)."""
    _init_small_primes()
    agree = 0
    bad: List[int] = []
    for p, bit in chunk:
        a = (p + 3) // 4
        pred = any(q % 3 == 2 for q in factorize(a))
        if pred == bool(bit):
            agree += 1
        else:
            bad.append(p)
    return (len(chunk), agree, bad)


def validate_theorem_R3(masks: Dict[int, int], workers: int = 4,
                        progress: bool = True) -> Dict:
    """Check Theorem 2 against every prime in the mask table."""
    items = [(p, m & 1) for p, m in masks.items()]
    n_chunks = workers * 8
    cs = (len(items) + n_chunks - 1) // n_chunks
    chunks = [items[i:i + cs] for i in range(0, len(items), cs)]
    total = agree = 0
    disagreements: List[int] = []
    t0 = time.time()
    from multiprocessing import Pool
    with Pool(workers) as pool:
        for nc, na, bad in pool.imap_unordered(_r3_worker, chunks):
            total += nc
            agree += na
            disagreements.extend(bad)
            if progress:
                print(f"[thm2] {total:,}/{len(items):,} "
                      f"({time.time()-t0:.0f}s)", flush=True)
    return {"checked": total, "agree": agree,
            "disagreements": sorted(disagreements)[:50]}


# --- Type I/II rates and Prop 1/3 validation over samples ------------------

def _cls_worker(args: Tuple[int, List[Tuple[int, int]]]
                ) -> Tuple[int, Counter, List[int], int, int]:
    """For residual R and sample [(p, works_bit)]: classify failures and
    check Prop 3 on successes (violations = primes that fail while having a
    Prop-3 class factor => would falsify Prop 3)."""
    R, sample = args
    _init_small_primes()
    cnt: Counter = Counter()
    prop3_false: List[int] = []
    succ_with_prop3 = succ_total = 0
    for p, works in sample:
        if works:
            succ_total += 1
            a = (p + R) // 4
            t = (-pow(4, -1, R) * p * p) % R
            pinv = pow(p, -1, R)
            S = {t, (t * pinv) % R, (t * pinv * pinv) % R}
            if any((q % R) in S for q in factorize(a)):
                succ_with_prop3 += 1
        else:
            info = classify_failure(p, R)
            cnt[info["type"]] += 1
            if info["prop3_violations"]:
                prop3_false.append(p)
    return (R, cnt, prop3_false, succ_with_prop3, succ_total)


def failure_taxonomy(masks: Dict[int, int], residuals: Sequence[int],
                     sample_step: int = 20, workers: int = 4) -> Dict:
    """Type I/II failure rates per residual over a systematic sample."""
    primes = sorted(masks)
    sample = primes[::sample_step]
    jobs = []
    for R in residuals:
        bit = 1 << R_INDEX[R]
        jobs.append((R, [(p, masks[p] & bit) for p in sample]))
    out: Dict[str, Dict] = {}
    from multiprocessing import Pool
    with Pool(min(workers, len(jobs))) as pool:
        for R, cnt, p3false, s3, st in pool.imap_unordered(_cls_worker, jobs):
            nfail = cnt["I"] + cnt["II"]
            out[str(R)] = {
                "sampled": len(sample),
                "failures": nfail,
                "type_I": cnt["I"],
                "type_II": cnt["II"],
                "type_I_share": round(cnt["I"] / nfail, 4) if nfail else None,
                "prop3_violations": p3false,      # must be []
                "success_with_prop3_class": s3,   # Prop-3 hits among successes
                "successes": st,
            }
    return out


# --- decay of failure rates & the growth model -----------------------------

def binned_failure_rates(masks: Dict[int, int], n_bins: int = 12
                         ) -> Dict[str, object]:
    """Per-residual failure rates in logarithmic bins of p.

    Sieve prediction: f_R(x) ~ C_R (log x)^(−κ_R); for R=3, κ = 1/2 exactly
    (Landau/Selberg–Delange for 'all prime factors ≡ 1 mod 3').
    """
    primes = sorted(masks)
    lo, hi = math.log(primes[0]), math.log(primes[-1] + 1)
    edges = [math.exp(lo + (hi - lo) * i / n_bins) for i in range(n_bins + 1)]
    bins: List[List[int]] = [[] for _ in range(n_bins)]
    bi = 0
    for p in primes:
        while p >= edges[bi + 1]:
            bi += 1
        bins[bi].append(p)
    table = []
    for i, bp in enumerate(bins):
        if not bp:
            continue
        row = {"lo": int(edges[i]), "hi": int(edges[i + 1]), "count": len(bp),
               "mid_logp": round((math.log(edges[i]) + math.log(edges[i+1])) / 2, 3)}
        rates = {}
        for j, R in enumerate(R_LIST):
            bit = 1 << j
            fails = sum(1 for p in bp if not (masks[p] & bit))
            rates[str(R)] = round(fails / len(bp), 5)
        row["fail_rates"] = rates
        table.append(row)

    # Fit kappa for each R: ln f = ln C − κ ln ln x  (least squares).
    fits = {}
    for R in R_LIST:
        xs, ys = [], []
        for row in table:
            f = row["fail_rates"][str(R)]
            if f > 0:
                xs.append(math.log(row["mid_logp"]))
                ys.append(math.log(f))
        if len(xs) >= 3:
            n = len(xs)
            mx, my = sum(xs) / n, sum(ys) / n
            sxx = sum((x - mx) ** 2 for x in xs)
            sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
            slope = sxy / sxx if sxx else 0.0
            fits[str(R)] = {"kappa": round(-slope, 3),
                            "C": round(math.exp(my - slope * mx), 3)}
    return {"bins": table, "power_fits": fits}


def record_model(masks: Dict[int, int], binned: Dict,
                 predict_to: float = 1e10) -> Dict:
    """Independence model: P(min R > B at p) = ∏_{R<=B} f_R(p).

    Validated in-sample (expected vs observed counts of min R > B), then
    extrapolated to `predict_to` using the fitted power laws to predict
    whether the record 107 falls in the next decade.
    """
    table = binned["bins"]
    fits = binned["power_fits"]

    # In-sample expected counts of "min R > B" for thresholds B.
    thresholds = [23, 47, 83, 103, 107]
    expected = {B: 0.0 for B in thresholds}
    for row in table:
        for B in thresholds:
            prod = 1.0
            for R in R_LIST:
                if R <= B:
                    prod *= row["fail_rates"][str(R)]
            expected[B] += row["count"] * prod
    observed = {B: sum(1 for p, m in masks.items()
                       if all(m >> i & 1 == 0
                              for i, R in enumerate(R_LIST) if R <= B))
                for B in thresholds}

    # Extrapolate to predict_to: hard primes have density 6/φ(840) = 1/32
    # among integers ~ li-style; count via dyadic slices of [1e9, predict_to].
    def f_R_at(R: int, x: float) -> float:
        fit = fits.get(str(R))
        if not fit:
            return 0.0
        return min(1.0, fit["C"] * math.log(x) ** (-fit["kappa"]))

    n_slices = 40
    lo, hi = math.log(1e9), math.log(predict_to)
    exp_beyond: Dict[int, float] = {B: 0.0 for B in thresholds}
    for s in range(n_slices):
        x0, x1 = math.exp(lo + (hi - lo) * s / n_slices), \
                 math.exp(lo + (hi - lo) * (s + 1) / n_slices)
        xm = math.sqrt(x0 * x1)
        # hard-prime count in slice ≈ (li(x1)-li(x0)) * 6/192 ≈ Δx/ln x /32
        n_hard = (x1 - x0) / math.log(xm) * (6 / 192)
        for B in thresholds:
            prod = 1.0
            for R in R_LIST:
                if R <= B:
                    prod *= f_R_at(R, xm)
            exp_beyond[B] += n_hard * prod
    return {
        "in_sample": {str(B): {"expected": round(expected[B], 2),
                               "observed": observed[B]}
                      for B in thresholds},
        "predicted_counts_1e9_to_%g" % predict_to:
            {str(B): round(v, 3) for B, v in exp_beyond.items()},
    }


# --- Theorem A' : machine-verified exact criterion for R = 7 ---------------

def verify_R7_finite() -> Dict:
    """Finite verification of the exact R=7 criterion for HARD primes.

    Success at R=7 depends only on the multiset of factor classes of
    m = p·a in (Z/7)* ≅ Z/6 (written in discrete-log coordinates w.r.t. the
    generator 3), with each factor usable in a divisor of m² with exponent
    at most twice its multiplicity.  Multiplicities cap at 3 (2·3 = 6 covers
    a full cycle), so the configuration space is finite.

    Structural constraints for hard primes:
      (i)  p ≡ QR (mod 7): the six Mordell classes mod 840 have
           p mod 7 ∈ {1, 2, 4};
      (ii) 2 | a: p ≡ 1 (mod 8) forces (p+7)/4 even — the class-2 (log-2)
           element always appears;
      (iii) consistency: a ≡ 4⁻¹p (mod 7), i.e. the factor logs sum to
           log(4⁻¹p).

    Claim verified: within these constraints, the target class −m is
    realizable by a bounded-exponent subproduct  ⟺  some factor log is odd
    (i.e. some prime factor of m is a non-residue mod 7).
    """
    from itertools import product as iproduct

    LOG = {1: 0, 3: 1, 2: 2, 6: 3, 4: 4, 5: 5}
    INV4 = 2  # 4^{-1} mod 7

    def reachable(mults, p_log):
        sums = {0}
        for v, mult in mults:
            cap = min(2 * mult, 6)
            sums = {(s + e * v) % 6 for s in sums for e in range(cap + 1)}
        return {(s + i * p_log) % 6 for s in sums for i in range(3)}

    checked = 0
    violations = []
    for mv in iproduct(range(4), repeat=6):
        if mv[2] == 0:      # (ii): class 2 must appear
            continue
        a_log = sum(v * m for v, m in zip(range(6), mv)) % 6
        for p_res in (1, 2, 4):   # (i)
            p_log = LOG[p_res]
            if a_log != LOG[(INV4 * p_res) % 7]:
                continue    # (iii)
            checked += 1
            has_odd = any(v % 2 == 1 and m > 0
                          for v, m in zip(range(6), mv))
            s = (a_log + p_log) % 6
            t = (s + 3) % 6         # log(−m) = log m + log(−1), log 6 = 3
            mults = [(v, m) for v, m in zip(range(6), mv) if m > 0]
            ok = t in reachable(mults, p_log)
            if has_odd != ok:
                violations.append({"mv": mv, "p_res": p_res,
                                   "has_odd": has_odd, "reachable": ok})
    return {"checked": checked, "violations": violations,
            "theorem_holds": not violations}


# --- the four critical primes ---------------------------------------------

CRITICAL = [8803369, 142361209, 287567281, 794037841]


def critical_report(masks: Dict[int, int]) -> List[Dict]:
    _init_small_primes()
    out = []
    for p in CRITICAL:
        m = masks[p]
        entries = []
        for i, R in enumerate(R_LIST):
            if m >> i & 1:
                entries.append({"R": R, "status": "works"})
            else:
                info = classify_failure(p, R)
                entries.append({
                    "R": R, "status": "fails",
                    "type": info["type"],
                    "obstruction_prime": info["obstruction_prime"],
                    "a_factors": info["a_factors"],
                })
        n_type1 = sum(1 for e in entries
                      if e["status"] == "fails" and e["type"] == "I")
        n_fail = sum(1 for e in entries if e["status"] == "fails")
        out.append({"p": p, "p_mod_840": p % 840,
                    "failures": n_fail, "type_I": n_type1,
                    "type_II": n_fail - n_type1, "detail": entries})
    return out


# --- main ------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--masks", default="data/analysis/residual_masks_1e9.json.gz")
    ap.add_argument("--out", default=None, help="JSON output path")
    ap.add_argument("--skip-thm2", action="store_true",
                    help="skip the full 1.59M-prime Theorem-2 validation")
    ap.add_argument("--sample-step", type=int, default=20)
    args = ap.parse_args(argv)

    _init_small_primes()
    print("loading masks ...", flush=True)
    with gzip.open(args.masks, "rt") as f:
        masks = {int(k): int(v) for k, v in json.load(f).items()}
    print(f"{len(masks):,} primes", flush=True)

    result: Dict[str, object] = {}

    print("\n=== Theorem 2 (exact R=3 criterion) ===", flush=True)
    if not args.skip_thm2:
        t2 = validate_theorem_R3(masks)
        print(f"agree {t2['agree']:,}/{t2['checked']:,}; "
              f"disagreements: {t2['disagreements'] or 'NONE'}")
        result["theorem2"] = t2

    print("\n=== Failure taxonomy (Type I vs II) + Prop 1/3 validation ===",
          flush=True)
    tax_residuals = [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107]
    tax = failure_taxonomy(masks, tax_residuals, sample_step=args.sample_step)
    for R in tax_residuals:
        row = tax[str(R)]
        print(f"  R={R:>3}: failures {row['failures']:>6,} | "
              f"Type I {row['type_I']:>6,} ({row['type_I_share']}) | "
              f"Type II {row['type_II']:>6,} | "
              f"Prop3 violations: {row['prop3_violations'] or 'none'}")
    result["taxonomy"] = tax

    print("\n=== Binned failure rates & power-law fits ===", flush=True)
    binned = binned_failure_rates(masks)
    for R in ["3", "7", "11", "23", "47"]:
        if R in binned["power_fits"]:
            f = binned["power_fits"][R]
            print(f"  R={R:>3}: f(x) ≈ {f['C']} (log x)^(-{f['kappa']})")
    result["binned"] = binned

    print("\n=== Independence model: record prediction ===", flush=True)
    model = record_model(masks, binned)
    print(json.dumps(model, indent=2))
    result["record_model"] = model

    print("\n=== The four critical primes ===", flush=True)
    crit = critical_report(masks)
    for c in crit:
        print(f"  p={c['p']:,} (mod 840 = {c['p_mod_840']}): "
              f"{c['failures']} failures = {c['type_I']} Type I "
              f"+ {c['type_II']} Type II")
    result["critical"] = crit

    if args.out:
        with open(args.out, "w") as f:
            json.dump(result, f, indent=2)
        print(f"\nJSON written to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
