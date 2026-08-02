#!/usr/bin/env python3
"""Step-1 scans for the Burgess/reciprocity route.

Background (THEORY.md §2.10). Theorem J holds for composite R ≡ 3 (mod 4)
with Jacobi symbols: for q | (p+R)/4, (q|R) = (p|q). At a residual whose
exact criterion is a pure Jacobi dichotomy (success ⟺ a = (p+R)/4 has a
prime factor q with (q|R) = −1 — proved for R = 3, 7, 15), success is
therefore equivalent to: some prime factor q of the shifted value has
(p|q) = −1. Running this backwards: take the least prime q with
(p|q) = −1 (Burgess: q ≪ p^{1/(4√e)+ε}; GRH: q ≪ (log p)²) and the least
R ≡ −p (mod 4q); then q | (p+R)/4 and (q|R) = −1, so at that R the
all-Jacobi-QR (Type-I) failure mode is impossible.  Whether p succeeds at
the selected R then depends only on the finer failure modes (budget /
per-prime-r character).  This module measures, on the complete 10⁹
ground-truth masks:

  * burgess_census    — for every hard prime: the least Legendre
                        non-residue q, the selected residual R, success
                        at R, and the failure anatomy + retry ladder.
  * jacobi_purity_scan — per residual R ≤ 107: among sampled primes whose
                        shifted value HAS a Jacobi non-residue factor,
                        how often does R still fail ("budget in the
                        wild")?  Zero ⟹ operationally pure dichotomy.
  * dichotomy_config_scan — exact generic configuration-space verdicts
                        for prime R via finite_criterion_dp: a residual
                        with no odd-failure states is pure a fortiori.

Outputs are archived under data/analysis/burgess_scan_1e9.json.
"""

from __future__ import annotations

import gzip
import json
import time
from typing import Dict, List, Optional, Tuple

from erdos_straus.bulk_generate import _init_small_primes, factorize
from erdos_straus.analyze import R_LIST, R_INDEX
from erdos_straus.theory import jacobi, finite_criterion_dp, solvable_exact_general

# Hard primes are automatically QRs mod 3, 5, 7 (Corollary 2.3(i)), so the
# least Legendre non-residue search starts at 11; 3, 5, 7 are kept in the
# candidate list purely as a sanity check (they must never fire).
_Q_CANDIDATES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
                 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]


def least_legendre_nonresidue(p: int) -> Optional[int]:
    """The least odd prime q with Legendre (p|q) = -1, or None if beyond
    the candidate table (never observed below 10^9)."""
    for q in _Q_CANDIDATES:
        if jacobi(p % q, q) == -1:
            return q
    return None


def selected_residual(p: int, q: int) -> int:
    """The least R > 0 with R ≡ -p (mod 4q); automatically R ≡ 3 (mod 4)
    for p ≡ 1 (mod 4), and q | (p+R)/4."""
    return (-p) % (4 * q)


def _has_jacobi_nonresidue_factor(a: int, R: int) -> bool:
    return any(jacobi(f % R, R) == -1 for f in factorize(a))


def _per_prime_character_obstruction(p: int, a: int, R: int) -> List[int]:
    """Primes r | R with r ≡ 3 (mod 4) for which every prime factor of
    m = p*a is a QR mod r (the Prop-2.1 obstruction carriers)."""
    qs = set(factorize(a)) | {p}
    out = []
    for r in factorize(R):
        if r % 4 == 3 and all(jacobi(x % r, r) in (0, 1) for x in qs):
            out.append(r)
    return out


def burgess_census(masks: Dict[int, int], sample_step: int = 1,
                   progress: bool = True) -> Dict:
    """The Burgess-selected-residual census over the ground-truth masks."""
    _init_small_primes()
    t0 = time.time()
    primes = sorted(masks)[::sample_step]
    q_hist: Dict[int, int] = {}
    r_hist: Dict[int, int] = {}
    n = succ = out_of_range = 0
    failures: List[Dict] = []
    for i, p in enumerate(primes):
        q = least_legendre_nonresidue(p)
        assert q is not None and q >= 11, (p, q)
        R = selected_residual(p, q)
        q_hist[q] = q_hist.get(q, 0) + 1
        r_hist[R] = r_hist.get(R, 0) + 1
        n += 1
        if R <= 107:
            ok = bool(masks[p] >> R_INDEX[R] & 1)
        else:
            out_of_range += 1
            ok = solvable_exact_general(p, R)
        if ok:
            succ += 1
        else:
            failures.append({"p": p, "q": q, "R": R})
        if progress and (i + 1) % 200000 == 0:
            print(f"[census] {i+1:,}/{len(primes):,} "
                  f"({time.time()-t0:.0f}s, {len(failures)} failures)",
                  flush=True)

    # Failure anatomy and the retry ladder (aggregated).
    mech_hist: Dict[str, int] = {}
    shots_hist: Dict[str, int] = {}
    unresolved: List[Dict] = []
    sanity_bad = 0
    examples: List[Dict] = []
    for j, f in enumerate(failures):
        p, q, R = f["p"], f["q"], f["R"]
        a = (p + R) // 4
        fa = factorize(a)
        if not (q in fa and jacobi(q % R, R) == -1):
            sanity_bad += 1
        obst = _per_prime_character_obstruction(p, a, R)
        mech = "per_prime_character" if obst else "budget"
        mech_hist[mech] = mech_hist.get(mech, 0) + 1
        # Retry ladder within the same q: R, R+4q, R+8q, ... up to 400.
        shots = 1
        solved_at = None
        Rk = R + 4 * q
        while Rk <= 400 and solved_at is None:
            shots += 1
            if Rk <= 107:
                ok = bool(masks[p] >> R_INDEX[Rk] & 1)
            else:
                ok = solvable_exact_general(p, Rk)
            if ok:
                solved_at = Rk
            Rk += 4 * q
        key = str(shots) if solved_at is not None else "unresolved<=400"
        shots_hist[key] = shots_hist.get(key, 0) + 1
        if solved_at is None:
            unresolved.append({"p": p, "q": q, "R": R})
        if len(examples) < 40:
            examples.append({"p": p, "q": q, "R": R, "mechanism": mech,
                             "char_obstruction_primes": obst,
                             "a_factors": {str(k): v
                                           for k, v in sorted(fa.items())},
                             "retry_solved_at_R": solved_at})
        if progress and (j + 1) % 20000 == 0:
            print(f"[census/failures] {j+1:,}/{len(failures):,} "
                  f"({time.time()-t0:.0f}s)", flush=True)

    return {
        "sampled": n, "sample_step": sample_step,
        "success_at_selected_R": succ,
        "failures": len(failures),
        "success_rate": succ / n if n else None,
        "selected_R_beyond_masks": out_of_range,
        "q_histogram": dict(sorted(q_hist.items())),
        "selected_R_max": max(r_hist) if r_hist else None,
        "failure_mechanisms": mech_hist,
        "retry_shots_histogram": dict(sorted(shots_hist.items())),
        "unresolved_below_400": unresolved,
        "sanity_violations": sanity_bad,
        "failure_examples": examples,
        "secs": round(time.time() - t0, 1),
    }


def jacobi_purity_scan(masks: Dict[int, int], sample_step: int = 20,
                       progress: bool = True) -> Dict:
    """Per residual R ≤ 107: split sampled primes by C1 = "(p+R)/4 has a
    prime factor with Jacobi (q|R) = -1" and tabulate ground truth on each
    side.  C1-true failures are budget failures in the wild (zero ⟹
    operationally pure dichotomy); C1-false successes measure how much
    the p-power escape hatch contributes."""
    _init_small_primes()
    t0 = time.time()
    primes = sorted(masks)[::sample_step]
    stats = {R: {"c1_true": 0, "c1_true_fail": 0,
                 "c1_false": 0, "c1_false_succ": 0,
                 "c1_true_fail_examples": []} for R in R_LIST}
    for i, p in enumerate(primes):
        m = masks[p]
        for R in R_LIST:
            a = (p + R) // 4
            c1 = _has_jacobi_nonresidue_factor(a, R)
            ok = bool(m >> R_INDEX[R] & 1)
            s = stats[R]
            if c1:
                s["c1_true"] += 1
                if not ok:
                    s["c1_true_fail"] += 1
                    if len(s["c1_true_fail_examples"]) < 20:
                        s["c1_true_fail_examples"].append(p)
            else:
                s["c1_false"] += 1
                if ok:
                    s["c1_false_succ"] += 1
        if progress and (i + 1) % 10000 == 0:
            print(f"[purity] {i+1:,}/{len(primes):,} ({time.time()-t0:.0f}s)",
                  flush=True)
    out = {"sampled": len(primes), "sample_step": sample_step,
           "per_R": {}, "secs": round(time.time() - t0, 1)}
    for R in R_LIST:
        s = stats[R]
        out["per_R"][str(R)] = {
            **{k: v for k, v in s.items() if k != "c1_true_fail_examples"},
            "budget_in_wild_rate": (s["c1_true_fail"] / s["c1_true"]
                                    if s["c1_true"] else None),
            "examples": s["c1_true_fail_examples"],
            "operationally_pure": s["c1_true_fail"] == 0,
        }
    return out


def dichotomy_config_scan(r_list: Optional[List[int]] = None,
                          time_budget: float = 120.0) -> Dict:
    """Exact generic configuration-space verdicts for prime residuals via
    finite_criterion_dp: 'pure_generic' means no odd-failure state exists
    even before hard-prime structure is imposed (pure a fortiori)."""
    if r_list is None:
        r_list = [7, 11, 19, 23, 31, 43]
    out: Dict[str, Dict] = {}
    for R in r_list:
        t0 = time.time()
        try:
            r = finite_criterion_dp(R)
        except Exception as e:  # state blow-up guard for exploratory scan
            out[str(R)] = {"status": f"error: {e}"}
            continue
        tally = r.get("tally", {})
        odd_failures = sum(v for k, v in tally.items()
                           if k.startswith("fail") and k != "fail_all_even")
        out[str(R)] = {"states": r.get("states"), "tally": tally,
                       "pure_generic": odd_failures == 0,
                       "secs": round(time.time() - t0, 1)}
        if time.time() - t0 > time_budget:
            break
    return out


def main() -> int:
    _init_small_primes()
    print("loading masks ...", flush=True)
    with gzip.open("data/analysis/residual_masks_1e9.json.gz", "rt") as f:
        masks = {int(k): int(v) for k, v in json.load(f).items()}
    print(f"{len(masks):,} primes", flush=True)

    result: Dict[str, object] = {}
    print("\n=== generic configuration-space verdicts (prime R) ===",
          flush=True)
    result["config_scan"] = dichotomy_config_scan()
    for R, v in result["config_scan"].items():
        print(f"  R={R}: {v}", flush=True)

    print("\n=== Jacobi purity scan (step 20) ===", flush=True)
    result["purity"] = jacobi_purity_scan(masks, sample_step=20)
    for R, v in result["purity"]["per_R"].items():
        print(f"  R={R:>3}: C1-true {v['c1_true']:>6}, budget-in-wild "
              f"{v['c1_true_fail']:>4}  pure={v['operationally_pure']}",
              flush=True)

    print("\n=== Burgess census (all primes) ===", flush=True)
    result["census"] = burgess_census(masks, sample_step=1)
    c = result["census"]
    print(f"  success at selected R: {c['success_at_selected_R']:,} / "
          f"{c['sampled']:,}  (failures: {c['failures']})", flush=True)

    with open("data/analysis/burgess_scan_1e9.json", "w") as f:
        json.dump(result, f, indent=1)
    print("\nwrote data/analysis/burgess_scan_1e9.json", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
