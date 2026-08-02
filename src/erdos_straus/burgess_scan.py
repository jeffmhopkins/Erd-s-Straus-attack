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


# --- Scaled census: direct computation beyond the 10^9 masks --------------
#
# Above 10^9 there are no full solvability masks, so success at the
# selected residual is computed directly with the composite-R exact engine
# (solvable_exact_general; factorization by trial division works to
# p < 10^11 since a = (p+R)/4 < 158,200^2).  Primes are drawn (i) as a
# systematic window sample across each decade and (ii) as the COMPLETE
# 10^11 deep tail (R_min >= 43), whose primes fail every small residual
# and are the ladder's adversarial population.

def census_one(p: int, cap: int = 400) -> Dict:
    """Full ladder outcome for a single hard prime: first-q selected
    residual, same-q ladder, then subsequent non-residues, rungs <= cap."""
    q1 = least_legendre_nonresidue(p)
    assert q1 is not None
    R1 = selected_residual(p, q1)
    ok1 = solvable_exact_general(p, R1)
    shots = 1
    solved_R: Optional[int] = R1 if ok1 else None
    solved_q = q1
    if solved_R is None:
        Rk = R1 + 4 * q1
        while Rk <= cap and solved_R is None:
            shots += 1
            if solvable_exact_general(p, Rk):
                solved_R = Rk
            else:
                Rk += 4 * q1
        if solved_R is None:
            for q in _Q_CANDIDATES:
                if q <= q1 or jacobi(p % q, q) != -1:
                    continue
                Rk = selected_residual(p, q)
                while Rk <= cap:
                    shots += 1
                    if solvable_exact_general(p, Rk):
                        solved_R, solved_q = Rk, q
                        break
                    Rk += 4 * q
                if solved_R is not None:
                    break
    return {"p": p, "q1": q1, "R1": R1, "first_shot": ok1,
            "solved_R": solved_R, "solved_q": solved_q, "shots": shots}


def _census_worker(chunk: List[int]) -> List[Dict]:
    _init_small_primes()
    return [census_one(p) for p in chunk]


def window_sample_primes(lo: int, hi: int, n_windows: int,
                         per_window: int = 4) -> List[int]:
    """Systematic sample: the first `per_window` hard primes at or after
    each of n_windows evenly spaced points of [lo, hi)."""
    import sympy
    hard = {1, 121, 169, 289, 361, 529}
    out: List[int] = []
    step = (hi - lo) // n_windows
    for i in range(n_windows):
        x = lo + i * step
        n = x - x % 840
        found = 0
        while found < per_window:
            for h in sorted(hard):
                c = n + h
                if c >= x and c < hi and sympy.isprime(c):
                    out.append(c)
                    found += 1
                    if found >= per_window:
                        break
            n += 840
    return out


def scaled_census(primes: List[int], workers: int = 4,
                  progress: bool = True, tag: str = "") -> Dict:
    """Aggregate ladder census over an explicit prime list (any size)."""
    from multiprocessing import Pool
    t0 = time.time()
    cs = max(1, len(primes) // (workers * 16))
    chunks = [primes[i:i + cs] for i in range(0, len(primes), cs)]
    rows: List[Dict] = []
    with Pool(workers) as pool:
        for out in pool.imap_unordered(_census_worker, chunks):
            rows.extend(out)
            if progress:
                print(f"[scaled{('/' + tag) if tag else ''}] "
                      f"{len(rows):,}/{len(primes):,} "
                      f"({time.time()-t0:.0f}s)", flush=True)
    n = len(rows)
    first = sum(r["first_shot"] for r in rows)
    solved = sum(r["solved_R"] is not None for r in rows)
    q1_hist: Dict[int, int] = {}
    shots_hist: Dict[int, int] = {}
    second_q = 0
    unresolved: List[int] = []
    for r in rows:
        q1_hist[r["q1"]] = q1_hist.get(r["q1"], 0) + 1
        if r["solved_R"] is None:
            unresolved.append(r["p"])
        else:
            shots_hist[r["shots"]] = shots_hist.get(r["shots"], 0) + 1
            if r["solved_q"] != r["q1"]:
                second_q += 1
    return {"tag": tag, "sampled": n,
            "first_shot_success": first,
            "first_shot_rate": first / n if n else None,
            "ladder_solved": solved,
            "ladder_rate": solved / n if n else None,
            "resolved_by_later_q": second_q,
            "unresolved_cap400": unresolved,
            "q1_histogram": dict(sorted(q1_hist.items())),
            "shots_histogram": dict(sorted(shots_hist.items())),
            "secs": round(time.time() - t0, 1)}


# --- Structural characterization of budget failures -----------------------
#
# For a failing (p, q, R) at the selected residual, the reach diagnostics
# separate three layers of obstruction and measure the configuration's
# anatomy: the size of its non-identity support, the multiplicity
# structure of its Jacobi-non-residue part, how many unit classes the
# (budgeted) reach set misses, and whether the target would be reached
# with UNBOUNDED factor exponents (true budget failure) or lies outside
# the generated subgroup altogether (subgroup miss - a stronger, exact
# obstruction that no exponent budget can cure).

def reach_diagnostics(p: int, R: int) -> Dict:
    import math as _m
    a = (p + R) // 4
    fa = factorize(a)
    units = [x for x in range(1, R) if _m.gcd(x, R) == 1]
    pl = p % R
    target = (-p * a) % R

    # Budgeted reach (exactly as solvable_exact_general computes it).
    S = {1}
    for qf, e in fa.items():
        v = qf % R
        if v == 1:
            continue
        o = 1
        x = v
        while x != 1:
            x = x * v % R
            o += 1
        cap = min(2 * e, o - 1)
        powers = [pow(v, k, R) for k in range(cap + 1)]
        S = {s * y % R for s in S for y in powers}
    S3 = {s * pow(pl, i, R) % R for s in S for i in range(3)}

    # Unbounded-budget reach: subgroup generated by the factor classes,
    # times the structural p-powers {1, p, p^2}.
    H = {1}
    for qf in fa:
        v = qf % R
        if v == 1:
            continue
        newH = set(H)
        frontier = set(H)
        while frontier:
            nxt = {h * v % R for h in frontier} - newH
            newH |= nxt
            frontier = nxt
        H = newH
    H3 = {h * pow(pl, i, R) % R for h in H for i in range(3)}

    nqr = {qf: e for qf, e in fa.items() if jacobi(qf % R, R) == -1}
    support = {qf % R for qf in fa if qf % R != 1}
    return {
        "support_size": len(support),
        "n_factors": sum(fa.values()),
        "n_nqr_distinct": len(nqr),
        "nqr_total_mult": sum(nqr.values()),
        "reach_size": len(S3), "units": len(units),
        "missed": len(units) - len(S3),
        "target_reached": target in S3,
        "true_budget": target in H3 and target not in S3,
        "subgroup_miss": target not in H3,
    }


def characterize_budget_failures(masks: Dict[int, int],
                                 progress: bool = True) -> Dict:
    """Re-derive the selected-residual failures below 10^9 and profile
    their configurations, with a matched success control group."""
    _init_small_primes()
    t0 = time.time()
    fails: List[Tuple[int, int, int]] = []
    ctrl: List[Tuple[int, int, int]] = []
    for i, p in enumerate(sorted(masks)):
        q = least_legendre_nonresidue(p)
        R = selected_residual(p, q)
        if R <= 107:
            ok = bool(masks[p] >> R_INDEX[R] & 1)
        else:
            ok = solvable_exact_general(p, R)
        if not ok:
            fails.append((p, q, R))
        elif i % 19 == 0:
            ctrl.append((p, q, R))
    print(f"[chars] {len(fails):,} failures, {len(ctrl):,} controls "
          f"({time.time()-t0:.0f}s)", flush=True)

    def profile(items, label):
        agg = {"n": 0, "support_hist": {}, "nqr_mult_hist": {},
               "missed_hist": {}, "true_budget": 0, "subgroup_miss": 0,
               "reached": 0, "q_only_nqr_mult1": 0}
        for k, (p, q, R) in enumerate(items):
            d = reach_diagnostics(p, R)
            agg["n"] += 1
            for key, h in (("support_size", "support_hist"),
                           ("nqr_total_mult", "nqr_mult_hist"),
                           ("missed", "missed_hist")):
                v = str(min(d[key], 30))
                agg[h][v] = agg[h].get(v, 0) + 1
            agg["true_budget"] += d["true_budget"]
            agg["subgroup_miss"] += d["subgroup_miss"]
            agg["reached"] += d["target_reached"]
            if d["n_nqr_distinct"] == 1 and d["nqr_total_mult"] == 1:
                agg["q_only_nqr_mult1"] += 1
            if progress and (k + 1) % 20000 == 0:
                print(f"[chars/{label}] {k+1:,}/{len(items):,} "
                      f"({time.time()-t0:.0f}s)", flush=True)
        for h in ("support_hist", "nqr_mult_hist", "missed_hist"):
            agg[h] = dict(sorted(agg[h].items(), key=lambda kv: int(kv[0])))
        return agg

    out = {"failures": profile(fails, "fail"),
           "successes_control": profile(ctrl, "ctrl"),
           "secs": round(time.time() - t0, 1)}
    # Rung-correlation: per-rung failure rate conditioned on q1.
    byq: Dict[int, List[int]] = {}
    for p, q, R in fails:
        byq.setdefault(q, []).append(p)
    out["failures_by_q1"] = {str(q): len(v) for q, v in sorted(byq.items())}
    return out


def proxy_ratio_scan(masks: Dict[int, int], sample_step: int = 20) -> Dict:
    """Measure Hypothesis P (THEORY.md 2.10): the ratio of true rung
    failures to their sieve-defined necessary condition (avoidance of the
    Prop 2.2 classes), at rungs 0 and 1 of the selected ladder."""
    _init_small_primes()

    def sclasses(p, R):
        t = (-pow(4, -1, R) * p * p) % R
        pinv = pow(p, -1, R)
        return {t, t * pinv % R, t * pinv * pinv % R}

    def avoid(p, R):
        S = sclasses(p, R)
        return not any(u % R in S for u in factorize((p + R) // 4))

    def fails(p, R):
        if R <= 107 and R in R_INDEX:
            return not (masks[p] >> R_INDEX[R] & 1)
        return not solvable_exact_general(p, R)

    n = av0 = f0 = av01 = e1_av1 = e1_f1 = sanity = 0
    for p in sorted(masks)[::sample_step]:
        q = least_legendre_nonresidue(p)
        R0 = selected_residual(p, q)
        R1 = R0 + 4 * q
        n += 1
        a0, ff0 = avoid(p, R0), fails(p, R0)
        if ff0 and not a0:
            sanity += 1
        if a0:
            av0 += 1
            if avoid(p, R1):
                av01 += 1
        if ff0:
            f0 += 1
            if avoid(p, R1):
                e1_av1 += 1
            if fails(p, R1):
                e1_f1 += 1
    return {"sampled": n, "sanity_violations": sanity,
            "avoid0": av0, "fail0": f0,
            "P_rung0": f0 / av0 if av0 else None,
            "proxy_decay_rung1": av01 / av0 if av0 else None,
            "true_decay_rung1": e1_f1 / f0 if f0 else None,
            "P_rung1_within_fail0": e1_f1 / e1_av1 if e1_av1 else None}


def _proxy_worker(chunk: List[int]) -> Tuple[int, int, int, int, int, int]:
    """Tallies (n, avoid0, fail0, avoid01, fail0_avoid1, fail0_fail1)."""
    _init_small_primes()
    n = av0 = f0 = av01 = f0a1 = f0f1 = 0
    for p in chunk:
        q = least_legendre_nonresidue(p)
        R0 = selected_residual(p, q)
        R1 = R0 + 4 * q

        def sclasses(R):
            t = (-pow(4, -1, R) * p * p) % R
            pinv = pow(p, -1, R)
            return {t, t * pinv % R, t * pinv * pinv % R}

        def avoid(R):
            S = sclasses(R)
            return not any(u % R in S for u in factorize((p + R) // 4))

        n += 1
        a0 = avoid(R0)
        f = not solvable_exact_general(p, R0)
        if a0:
            av0 += 1
            if avoid(R1):
                av01 += 1
        if f:
            f0 += 1
            if avoid(R1):
                f0a1 += 1
            if not solvable_exact_general(p, R1):
                f0f1 += 1
    return (n, av0, f0, av01, f0a1, f0f1)


def proxy_ratio_scan_scaled(primes: List[int], workers: int = 4,
                            tag: str = "") -> Dict:
    """Hypothesis-P measurement over an explicit prime list, mask-free."""
    from multiprocessing import Pool
    t0 = time.time()
    cs = max(1, len(primes) // (workers * 8))
    chunks = [primes[i:i + cs] for i in range(0, len(primes), cs)]
    n = av0 = f0 = av01 = f0a1 = f0f1 = 0
    with Pool(workers) as pool:
        for t in pool.imap_unordered(_proxy_worker, chunks):
            n += t[0]; av0 += t[1]; f0 += t[2]
            av01 += t[3]; f0a1 += t[4]; f0f1 += t[5]
    return {"tag": tag, "sampled": n,
            "avoid0_rate": av0 / n, "fail0_rate": f0 / n,
            "P_rung0": f0 / av0 if av0 else None,
            "proxy_decay_rung1": av01 / av0 if av0 else None,
            "true_decay_rung1": f0f1 / f0 if f0 else None,
            "P_rung1_within_fail0": f0f1 / f0a1 if f0a1 else None,
            "secs": round(time.time() - t0, 1)}
