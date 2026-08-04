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
  * admissibility_census — how many first rungs the lower-bound theorem
                        of §5 (paper Thm 5.8, THEORY.md §2.10) actually
                        reaches: the (A1)–(A3) admissibility predicate on
                        the class c mod M, and in particular whether the
                        family it counts is nonempty.

Outputs are archived under data/analysis/burgess_scan_1e9.json.

Archive regeneration (CLI)
--------------------------
Every archive under data/analysis/ produced by this module has a
subcommand that regenerates it (``python -m erdos_straus.burgess_scan
<command> --help`` for the knobs; defaults reproduce the archives):

  census        -> data/analysis/burgess_scan_1e9.json
                   Exhaustive 10^9 census + purity + config scans
                   (default command; multi-hour runtime).
  scaled        -> data/analysis/burgess_scan_1e10_1e11.json
                   Window samples 10^9..10^11 plus the complete 10^11
                   deep tail (needs data/hard_primes_1e11_minimalR.tail.json).
  failures      -> data/analysis/burgess_failures_1e9.json
                   Reach diagnostics of the selected-residual failures.
  proxy         -> data/analysis/burgess_proxy_1e9.json
                   Hypothesis-P proxy-ratio scan on the 10^9 masks.
  proxy-scaled  -> data/analysis/burgess_proxy_scaled.json
                   Mask-free Hypothesis-P scan on window samples to 10^11.
  admissibility -> data/analysis/burgess_admissibility.json
                   Theorem 5.8 (A1)-(A3) admissibility census of the
                   first rungs below 2*10^7 (Remark 5.9's figures).

Invoking the module with no arguments runs ``census`` (the historical
behavior).
"""

from __future__ import annotations

import argparse
import gzip
import json
import sys
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
        while found < per_window and n < hi:
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


# --- Admissibility of a first rung (paper Thm 5.8 / Rem 5.9) --------------
#
# Theorem 5.8 (THEORY.md §2.10, the corrected "Theorem P1") gives an
# unconditional lower bound #E_0(x) >> x/(log x)^{3/2} on the failures of
# the FIRST rung, but only on classes c mod M — M = 840·∏_{11≤ℓ≤q} ℓ, the
# modulus of the proof of Theorem B_1 — that are *admissible*: R_0 must
# have a prime factor r_1 ≡ 3 (mod 4) with
#
#   (A1) (q|r_1) = +1;
#   (A2) (ℓ|r_1) = +1 for EVERY prime ℓ ≤ q that the class forces to
#        divide a = (p+R_0)/4;
#   (A3) either r_1 ≡ 3 (mod 8) with a odd, or r_1 ≡ 7 (mod 8) with a even.
#
# (A2) is the clause whose omission made the printed "P1" false: the
# counted family is {p ≡ c : every prime factor of a is a QR mod r_1}, and
# a single class-forced ℓ with (ℓ|r_1) = −1 empties it (Remark 5.9's
# q = 23, R_0 = 35, r_1 = 7 example).  This section makes the predicate and
# its census reproducible; the archive is burgess_admissibility.json.
#
# Two structural remarks the code leans on:
#   * q | a always (that is how R_0 is selected), so (A1) is precisely the
#     ℓ = q instance of (A2);
#   * hard primes are ≡ 1 (mod 8), so a is even iff R_0 ≡ 7 (mod 8), and
#     the ℓ = 2 instance of (A2) — (2|r_1) = +1 whenever 2 | a, i.e.
#     r_1 ≡ 7 (mod 8) whenever a is even — is what (A3) encodes.  (A3) as
#     printed is strictly stronger than that ℓ = 2 instance: it also
#     discards the "mixed" configuration r_1 ≡ 7 (mod 8) with a odd, which
#     is 2-adically fine but falls outside the citable form of [FHRSS].
#     Both counts are reported; see `definitions` in the archive.
#
# If R_0 is prime then its only prime factor is r_1 = R_0, and Theorem J
# gives (q|R_0) = (p|q) = −1 (q | a and R_0 ≡ 3 mod 4), so (A1) fails
# outright: prime R_0 is never admissible.

# 2 together with the odd primes of the least-non-residue table.
_PRIMES_TO_113 = (2,) + tuple(_Q_CANDIDATES)


def class_modulus(q: int) -> int:
    """M = 840·∏_{11 ≤ ℓ ≤ q} ℓ, the modulus of the proof of Theorem B_1:
    the condition q(p) = q is a union of classes mod M, and fixing one
    fixes R_0 and every residue p mod ℓ for ℓ ≤ q."""
    M = 840
    for ell in _Q_CANDIDATES:
        if 11 <= ell <= q:
            M *= ell
    return M


def forced_small_primes(p: int, R0: int, q: int) -> List[int]:
    """The primes ℓ ≤ q that the class of p modulo M = class_modulus(q)
    FORCES to divide a = (p + R_0)/4 — the ℓ's quantified over in (A2).

    Interpretation (this is what "forced by the class" means, and it is
    the whole content of clause (A2)).  A prime ℓ divides a for ALL primes
    in the class c = p mod M, not merely for this one, iff the class fixes
    p mod ℓ and p ≡ −R_0 (mod ℓ).  Concretely, since 4 is invertible mod
    every odd ℓ,

        ℓ | a  ⟺  p ≡ −R_0 (mod ℓ)      (ℓ odd),
        2 | a  ⟺  p ≡ −R_0 (mod 8)      (ℓ = 2, because a = (p+R_0)/4),

    and M = 840·∏_{11 ≤ ℓ ≤ q} ℓ is divisible by 8 and by every odd prime
    ℓ ≤ q (840 = 2³·3·5·7 supplies 2, 3, 5, 7).  So for every prime ℓ ≤ q
    the condition is constant on the class — true for all of it or for
    none of it — and is decidable from the single representative p.  That
    is why a per-prime computation answers a per-class question here, and
    why (A2) is checkable at all.

    Primes ℓ > q are NOT forced: the class says nothing about p mod ℓ, so
    such an ℓ divides a for some members of the class and not others, and
    imposes no condition on r_1.

    Two entries deserve names: ℓ = q is always present (q | a by the
    construction of R_0), so (A1) is exactly the ℓ = q instance; and
    ℓ = 2 is present iff R_0 ≡ 7 (mod 8) (hard primes are ≡ 1 mod 8), the
    instance that (A3) encodes.
    """
    out: List[int] = []
    for ell in _PRIMES_TO_113:
        if ell > q:
            break
        if (p + R0) % (8 if ell == 2 else ell) == 0:
            out.append(ell)
    return out


def admissibility(p: int) -> Dict:
    """The Theorem 5.8 admissibility record of p's first rung.

    Returns q, R_0, a, the class-forced small primes, and one sub-record
    per candidate r_1 (prime factor of R_0 with r_1 ≡ 3 mod 4) carrying
    (A1), (A2), the 2-adic verdicts and the resulting 2-adic case:

      "A"        r_1 ≡ 3 (mod 8), a odd   — (A3) as printed
      "B"        r_1 ≡ 7 (mod 8), a even  — (A3) as printed
      "mixed"    r_1 ≡ 7 (mod 8), a odd   — 2-adically admissible (2 ∤ a,
                 so ℓ = 2 imposes nothing) but outside (A3) as printed
      "excluded" r_1 ≡ 3 (mod 8), a even  — (2|r_1) = −1 with 2 | a: the
                 family is empty

    ``nonempty`` is (A1) ∧ (A2) ∧ (the ℓ = 2 instance), i.e. every
    class-forced prime is a QR mod r_1 — the exact condition for the
    counted family to be nonempty.  ``a3_as_printed`` additionally demands
    case A or case B.  The top-level summary flags are the existential
    over the candidates.
    """
    q = least_legendre_nonresidue(p)
    assert q is not None, p
    R0 = selected_residual(p, q)
    a = (p + R0) // 4
    a_even = a % 2 == 0
    forced = forced_small_primes(p, R0, q)
    fR0 = factorize(R0)
    cands: List[Dict] = []
    for r1 in sorted(fR0):
        if r1 % 4 != 3:
            continue
        a1 = jacobi(q % r1, r1) == 1
        bad = [ell for ell in forced
               if ell != 2 and jacobi(ell % r1, r1) != 1]
        a2 = not bad
        two_adic = (not a_even) or r1 % 8 == 7
        if r1 % 8 == 3:
            case = "A" if not a_even else "excluded"
        else:
            case = "B" if a_even else "mixed"
        a3 = case in ("A", "B")
        cands.append({
            "r1": r1, "A1": a1, "A2": a2, "A2_violations": bad,
            "two_adic_ok": two_adic, "A3_as_printed": a3, "case": case,
            "nonempty": a1 and a2 and two_adic,
            "a3_as_printed_pass": a1 and a2 and a3,
        })
    ok = [c for c in cands if c["nonempty"]]
    return {
        "p": p, "q": q, "M": class_modulus(q), "R0": R0, "a": a,
        "a_even": a_even,
        "R0_factors": {str(k): v for k, v in sorted(fR0.items())},
        "R0_prime": len(fR0) == 1 and next(iter(fR0.values())) == 1,
        "forced_small_primes": forced,
        "r1_candidates": cands,
        "A1": any(c["A1"] for c in cands),
        "nonempty_family": bool(ok),
        "a3_as_printed": any(c["a3_as_printed_pass"] for c in cands),
        "selected_r1": ok[0]["r1"] if ok else None,
        "case": ok[0]["case"] if ok else None,
        "n_nonempty_candidates": len(ok),
    }


_ADMISSIBILITY_DEFINITIONS = {
    "hard_prime": "prime p with p mod 840 in {1,121,169,289,361,529}",
    "q": "least prime with Legendre (p|q) = -1 (least_legendre_nonresidue)",
    "R0": "least R > 0 with R = -p (mod 4q) (selected_residual); "
          "R0 = 3 (mod 4) and q | a = (p+R0)/4",
    "class_modulus_M": "840 * prod(primes 11 <= ell <= q); the class "
                       "c = p mod M fixes q, R0 and p mod ell for all "
                       "ell <= q",
    "forced": "prime ell <= q divides a for EVERY p in the class c mod M; "
              "equivalently p = -R0 (mod ell) for odd ell, p = -R0 "
              "(mod 8) for ell = 2. Primes ell > q are never forced.",
    "r1_candidates": "ALL prime factors r1 of R0 with r1 = 3 (mod 4); "
                     "admissibility is the existential over them",
    "A1": "(q|r1) = +1  [= the ell = q instance of (A2), since q | a "
          "always]",
    "A2": "(ell|r1) = +1 for every forced odd ell <= q (q included); a "
          "forced ell = r1 counts as a violation, (r1|r1) = 0",
    "A3_as_printed": "r1 = 3 (mod 8) with a odd, or r1 = 7 (mod 8) with "
                     "a even",
    "two_adic_ok": "the ell = 2 instance of (A2): (2|r1) = +1 whenever "
                   "2 | a, i.e. r1 = 7 (mod 8) whenever a is even. "
                   "Weaker than A3_as_printed: it also admits the "
                   "'mixed' case r1 = 7 (mod 8) with a odd.",
    "nonempty_family": "A1 and A2 and two_adic_ok - the exact condition "
                       "for {p = c (mod M) : every prime factor of a is "
                       "a QR mod r1} to be nonempty, since a violation "
                       "at a forced ell puts that ell in every member's "
                       "factorization",
    "case_split": "2-adic configuration of the selected r1: A (r1 = 3 "
                  "mod 8, a odd) / B (r1 = 7 mod 8, a even) / mixed "
                  "(r1 = 7 mod 8, a odd) / excluded (r1 = 3 mod 8, a "
                  "even, family empty)",
    "counting_unit": "one hard prime = one first rung; primes sharing a "
                     "class mod M give identical verdicts, so shares are "
                     "shares of first rungs exactly as in Remark 5.9",
}


def admissibility_census(limit: int = 2 * 10**7,
                         primes: Optional[List[int]] = None,
                         progress: bool = True,
                         max_exemplars: int = 50) -> Dict:
    """Census of Theorem 5.8 admissibility over the hard primes p ≤ limit.

    Aggregates: total hard primes; how many first rungs pass (A1) alone;
    how many have a NONEMPTY family (A1 ∧ (A2) ∧ the ℓ = 2 instance); how
    many additionally satisfy (A3) exactly as printed; the 2-adic case
    split; and how many have R_0 prime (for which no r_1 exists at all).
    """
    _init_small_primes()
    t0 = time.time()
    if primes is None:
        from erdos_straus.bulk_generate import hard_primes_upto
        primes = hard_primes_upto(limit)
    n = len(primes)
    n_a1 = n_nonempty = n_a3 = n_r0_prime = n_no_r1 = n_multi = 0
    cases: Dict[str, int] = {"A": 0, "B": 0, "mixed": 0}
    q_hist: Dict[int, int] = {}
    r0_hist_a1: Dict[int, int] = {}
    classes = set()
    exemplars: List[Dict] = []
    for i, p in enumerate(primes):
        rec = admissibility(p)
        q_hist[rec["q"]] = q_hist.get(rec["q"], 0) + 1
        if rec["R0_prime"]:
            n_r0_prime += 1
        if rec["A1"]:
            n_a1 += 1
            r0_hist_a1[rec["R0"]] = r0_hist_a1.get(rec["R0"], 0) + 1
        else:
            n_no_r1 += 1
        if rec["nonempty_family"]:
            n_nonempty += 1
            cases[rec["case"]] = cases.get(rec["case"], 0) + 1
            classes.add((rec["q"], rec["R0"], rec["selected_r1"]))
            if rec["n_nonempty_candidates"] > 1:
                n_multi += 1
            if len(exemplars) < max_exemplars:
                exemplars.append({
                    "p": p, "q": rec["q"], "R0": rec["R0"],
                    "r1": rec["selected_r1"], "case": rec["case"],
                    "a": rec["a"],
                    "a_factors": {str(k): v for k, v in
                                  sorted(factorize(rec["a"]).items())},
                    "forced_small_primes": rec["forced_small_primes"],
                    "A3_as_printed": rec["a3_as_printed"],
                })
        if rec["a3_as_printed"]:
            n_a3 += 1
        if progress and (i + 1) % 5000 == 0:
            print(f"[admissibility] {i+1:,}/{n:,} "
                  f"({time.time()-t0:.0f}s, A1 {n_a1}, "
                  f"nonempty {n_nonempty})", flush=True)

    def share(k: int) -> Optional[float]:
        return k / n if n else None

    return {
        "limit": limit,
        "hard_primes": n,
        "definitions": _ADMISSIBILITY_DEFINITIONS,
        "counts": {
            "A1_only": n_a1,
            "A1_only_share": share(n_a1),
            "nonempty_family": n_nonempty,
            "nonempty_family_share": share(n_nonempty),
            "a3_as_printed": n_a3,
            "a3_as_printed_share": share(n_a3),
            "case_split": cases,
            "R0_prime": n_r0_prime,
            "R0_prime_share": share(n_r0_prime),
            "no_r1_candidate_passing_A1": n_no_r1,
            "no_r1_candidate_passing_A1_share": share(n_no_r1),
            "distinct_admissible_classes_q_R0_r1": len(classes),
            "primes_with_two_nonempty_r1": n_multi,
        },
        "admissible_classes": sorted(list(c) for c in classes),
        "exemplars": exemplars,
        "q_histogram": dict(sorted(q_hist.items())),
        "R0_histogram_A1": dict(sorted(r0_hist_a1.items())),
        "secs": round(time.time() - t0, 1),
    }


# --- CLI: regeneration of the data/analysis archives -----------------------

_MASKS_1E9 = "data/analysis/residual_masks_1e9.json.gz"
_TAIL_1E11 = "data/hard_primes_1e11_minimalR.tail.json"

# Half-decade bins used for both scaled scans (window samples 10^9..10^11).
_SCALED_BINS = [(10**9, 3163 * 10**6, "1e9-3.2e9"),
                (3163 * 10**6, 10**10, "3.2e9-1e10"),
                (10**10, 3163 * 10**7, "1e10-3.2e10"),
                (3163 * 10**7, 10**11, "3.2e10-1e11")]


def _load_masks(path: str) -> Dict[int, int]:
    print(f"loading masks from {path} ...", flush=True)
    with gzip.open(path, "rt") as f:
        masks = {int(k): int(v) for k, v in json.load(f).items()}
    print(f"{len(masks):,} primes", flush=True)
    return masks


def _write_json(result: object, path: str) -> None:
    with open(path, "w") as f:
        json.dump(result, f, indent=1)
    print(f"\nwrote {path}", flush=True)


def _cmd_census(args: argparse.Namespace) -> int:
    """Regenerate burgess_scan_1e9.json (the historical default run)."""
    masks = _load_masks(args.masks)

    result: Dict[str, object] = {}
    print("\n=== generic configuration-space verdicts (prime R) ===",
          flush=True)
    result["config_scan"] = dichotomy_config_scan()
    for R, v in result["config_scan"].items():
        print(f"  R={R}: {v}", flush=True)

    print(f"\n=== Jacobi purity scan (step {args.purity_step}) ===",
          flush=True)
    result["purity"] = jacobi_purity_scan(masks,
                                          sample_step=args.purity_step)
    for R, v in result["purity"]["per_R"].items():
        print(f"  R={R:>3}: C1-true {v['c1_true']:>6}, budget-in-wild "
              f"{v['c1_true_fail']:>4}  pure={v['operationally_pure']}",
              flush=True)

    print("\n=== Burgess census (all primes) ===", flush=True)
    result["census"] = burgess_census(masks, sample_step=args.sample_step)
    c = result["census"]
    print(f"  success at selected R: {c['success_at_selected_R']:,} / "
          f"{c['sampled']:,}  (failures: {c['failures']})", flush=True)

    # Second-q ladder for the first-q-unresolved primes (archive key
    # "second_q_ladder"): rerun each through the full census_one ladder,
    # which continues onto later non-residues q, rungs <= 400.
    unresolved = c["unresolved_below_400"]
    still: List[int] = []
    for f in unresolved:
        if census_one(f["p"], cap=400)["solved_R"] is None:
            still.append(f["p"])
    note = ("every first-q-unresolved prime solves on a later non-residue "
            "q ladder, R <= 400" if not still else
            f"{len(still)} primes remain unresolved at R <= 400 on all "
            "candidate q ladders")
    c["second_q_ladder"] = {"resolved": len(unresolved) - len(still),
                            "still_unresolved": still, "note": note}
    print(f"  second-q ladder: {len(unresolved) - len(still):,} resolved, "
          f"{len(still)} still unresolved", flush=True)

    _write_json(result, args.out)
    return 0


def _cmd_scaled(args: argparse.Namespace) -> int:
    """Regenerate burgess_scan_1e10_1e11.json."""
    result: Dict[str, object] = {}
    for lo, hi, tag in _SCALED_BINS:
        t0 = time.time()
        print(f"=== sampling {tag} ===", flush=True)
        primes = window_sample_primes(lo, hi, args.windows, args.per_window)
        print(f"  {len(primes):,} primes sampled ({time.time()-t0:.0f}s)",
              flush=True)
        result[tag] = scaled_census(primes, workers=args.workers,
                                    progress=False, tag=tag)
        r = result[tag]
        print(f"  first-shot {r['first_shot_rate']:.4f}  ladder "
              f"{r['ladder_rate']:.5f}  unresolved "
              f"{len(r['unresolved_cap400'])}", flush=True)

    print("=== 10^11 deep tail (complete, R_min >= 43) ===", flush=True)
    with open(args.tail) as f:
        tail = json.load(f)
    entries = (tail["entries"]
               if isinstance(tail, dict) and "entries" in tail else tail)
    tp: List[int] = []
    rmin: Dict[int, int] = {}
    for e in entries:
        p = int(e["p"])
        tp.append(p)
        rmin[p] = int(e["R"])
    print(f"  {len(tp):,} tail primes", flush=True)

    # Integrity cross-check against the stored dataset: the engine must
    # agree that the stored R_min works, on a systematic sample.
    sample = tp[::200]
    bad = [p for p in sample if not solvable_exact_general(p, rmin[p])]
    print(f"  integrity check vs stored R_min: {len(sample)} sampled, "
          f"{len(bad)} disagreements", flush=True)
    assert not bad, bad[:5]

    result["tail_1e11"] = scaled_census(tp, workers=args.workers,
                                        progress=True, tag="tail")
    r = result["tail_1e11"]
    print(f"  tail: first-shot {r['first_shot_rate']:.4f}  ladder "
          f"{r['ladder_rate']:.5f}  unresolved "
          f"{len(r['unresolved_cap400'])}", flush=True)

    # For unresolved tail primes (if any): stored R_min for context, plus
    # an extended ladder with the rung cap raised past 400.
    result["tail_unresolved_rmin"] = {str(p): rmin[p]
                                      for p in r["unresolved_cap400"]}
    result["integrity_check"] = {"sampled": len(sample),
                                 "disagreements": len(bad)}
    if r["unresolved_cap400"]:
        ext: Dict[str, object] = {}
        worst = 0
        all_ok = True
        for p in r["unresolved_cap400"]:
            c1 = census_one(p, cap=args.extend_cap)
            ext[str(p)] = {"rmin": rmin[p],
                           "resolves_at_R": c1["solved_R"],
                           "with_q": c1["solved_q"]}
            if c1["solved_R"] is None:
                all_ok = False
            else:
                worst = max(worst, c1["solved_R"])
        ext["note"] = (f"all cap-400-unresolved primes resolve on an "
                       f"extended ladder; coverage is 100% at cap {worst}"
                       if all_ok else
                       f"some primes remain unresolved at cap "
                       f"{args.extend_cap}")
        result["tail_unresolved_extended"] = ext

    _write_json(result, args.out)
    return 0


def _cmd_failures(args: argparse.Namespace) -> int:
    """Regenerate burgess_failures_1e9.json."""
    masks = _load_masks(args.masks)
    result = characterize_budget_failures(masks)
    print(f"  failures profiled: {result['failures']['n']:,}  "
          f"controls: {result['successes_control']['n']:,}", flush=True)
    _write_json(result, args.out)
    return 0


def _cmd_proxy(args: argparse.Namespace) -> int:
    """Regenerate burgess_proxy_1e9.json."""
    masks = _load_masks(args.masks)
    result = proxy_ratio_scan(masks, sample_step=args.sample_step)
    print(f"  sampled {result['sampled']:,}  P_rung0={result['P_rung0']}",
          flush=True)
    _write_json(result, args.out)
    return 0


def _cmd_proxy_scaled(args: argparse.Namespace) -> int:
    """Regenerate burgess_proxy_scaled.json."""
    result: Dict[str, object] = {}
    for lo, hi, tag in _SCALED_BINS:
        print(f"=== sampling {tag} ===", flush=True)
        primes = window_sample_primes(lo, hi, args.windows, args.per_window)
        print(f"  {len(primes):,} primes sampled", flush=True)
        result[tag] = proxy_ratio_scan_scaled(primes, workers=args.workers,
                                              tag=tag)
        r = result[tag]
        print(f"  P_rung0 {r['P_rung0']}  proxy_decay "
              f"{r['proxy_decay_rung1']}", flush=True)
    _write_json(result, args.out)
    return 0


# Figures quoted in paper Remark 5.9 / THEORY.md §2.10, recorded verbatim
# so the archive states what it was checked against.
_PAPER_FIGURES = {
    "hard_primes": 39391,
    "A1_only": 2593,
    "A1_only_share": 0.066,
    "nonempty_family": 9,
    "nonempty_family_share": 0.00023,
    "case_split": {"A": 5, "B": 0, "mixed": 4},
    "R0_prime_share": 0.934,
}


def _cmd_admissibility(args: argparse.Namespace) -> int:
    """Regenerate burgess_admissibility.json."""
    result = admissibility_census(limit=args.limit,
                                  max_exemplars=args.max_exemplars)
    c = result["counts"]
    print(f"\nhard primes <= {args.limit:,}: {result['hard_primes']:,}",
          flush=True)
    print(f"  (A1) alone           : {c['A1_only']:,} "
          f"({100*c['A1_only_share']:.2f}%)", flush=True)
    print(f"  nonempty family      : {c['nonempty_family']:,} "
          f"({100*c['nonempty_family_share']:.4f}%)", flush=True)
    print(f"  (A3) exactly as printed: {c['a3_as_printed']:,}", flush=True)
    print(f"  case split           : {c['case_split']}", flush=True)
    print(f"  R0 prime             : {c['R0_prime']:,} "
          f"({100*c['R0_prime_share']:.2f}%)", flush=True)
    print(f"  no r1 passing (A1)   : "
          f"{c['no_r1_candidate_passing_A1']:,} "
          f"({100*c['no_r1_candidate_passing_A1_share']:.2f}%)", flush=True)

    # Honest comparison against the printed figures.
    comp: Dict[str, object] = {"quoted": _PAPER_FIGURES, "checks": {}}

    def chk(key, computed, quoted, tol):
        ok = abs(computed - quoted) <= tol
        comp["checks"][key] = {"computed": computed, "quoted": quoted,
                               "agrees": ok}
        return ok
    chk("hard_primes", result["hard_primes"],
        _PAPER_FIGURES["hard_primes"], 0)
    chk("A1_only", c["A1_only"], _PAPER_FIGURES["A1_only"], 0)
    chk("A1_only_share", round(c["A1_only_share"], 4),
        _PAPER_FIGURES["A1_only_share"], 5e-4)
    chk("nonempty_family", c["nonempty_family"],
        _PAPER_FIGURES["nonempty_family"], 0)
    chk("R0_prime_share", round(c["R0_prime_share"], 4),
        _PAPER_FIGURES["R0_prime_share"], 5e-4)
    comp["checks"]["case_split"] = {
        "computed": c["case_split"], "quoted": _PAPER_FIGURES["case_split"],
        "agrees": c["case_split"] == _PAPER_FIGURES["case_split"]}
    comp["notes"] = [
        "(A3) as PRINTED (case A or case B only) is satisfied by "
        f"{c['a3_as_printed']} first rungs, not "
        f"{_PAPER_FIGURES['nonempty_family']}: the quoted headline count "
        "includes the 'mixed' configuration r1 = 7 (mod 8) with a odd, "
        "which is 2-adically admissible (2 does not divide a, so ell = 2 "
        "imposes no condition) but is not one of the two cases (A3) "
        "lists. The quoted case split names those 4 mixed rungs "
        "explicitly, so the headline count is the nonempty-family count "
        "reported here.",
        "The quoted 'R0 is prime for 93.4% of hard primes' does NOT "
        f"match: R0 is prime for {c['R0_prime']:,} of "
        f"{result['hard_primes']:,} first rungs = "
        f"{100*c['R0_prime_share']:.1f}%. 93.4% is exactly "
        f"100% - 6.6% = the share of first rungs with NO r1 passing "
        f"(A1) ({c['no_r1_candidate_passing_A1']:,}/"
        f"{result['hard_primes']:,} = "
        f"{100*c['no_r1_candidate_passing_A1_share']:.1f}%). Prime R0 is "
        "a strict subset of that: prime R0 always fails (A1) (its only "
        "prime factor is r1 = R0, and Theorem J gives (q|R0) = (p|q) = "
        "-1), but composite R0 can fail (A1) too.",
    ]
    result["paper_comparison"] = comp
    for key, v in comp["checks"].items():
        flag = "ok " if v["agrees"] else "MISMATCH"
        print(f"  [{flag}] {key}: computed {v['computed']} vs quoted "
              f"{v['quoted']}", flush=True)
    _write_json(result, args.out)
    return 0


def _add_masks_out(sp: argparse.ArgumentParser, default_out: str) -> None:
    sp.add_argument("--masks", default=_MASKS_1E9,
                    help=f"ground-truth mask archive (default: {_MASKS_1E9})")
    sp.add_argument("--out", default=default_out,
                    help=f"output JSON path (default: {default_out})")


def main(argv: Optional[List[str]] = None) -> int:
    _init_small_primes()
    parser = argparse.ArgumentParser(
        prog="python -m erdos_straus.burgess_scan",
        description="Burgess/reciprocity scans; each subcommand "
                    "regenerates one archive under data/analysis/.",
        epilog="With no arguments, runs 'census' (historical behavior).")
    sub = parser.add_subparsers(dest="command", metavar="command")

    sp = sub.add_parser(
        "census",
        help="regenerate burgess_scan_1e9.json (exhaustive 10^9 census; "
             "multi-hour runtime)",
        description="Exhaustive Burgess census over the complete 10^9 "
                    "ground-truth masks, plus the Jacobi purity scan and "
                    "the generic configuration-space verdicts. This is "
                    "the default command and reproduces "
                    "data/analysis/burgess_scan_1e9.json. WARNING: at the "
                    "default sample-step 1 this walks all ~1.5M hard "
                    "primes with factorization and retry ladders - expect "
                    "a MULTI-HOUR runtime.")
    sp.add_argument("--sample-step", type=int, default=1,
                    help="census prime subsampling step (default: 1 = "
                         "exhaustive; larger values for a quick look)")
    sp.add_argument("--purity-step", type=int, default=20,
                    help="purity-scan subsampling step (default: 20)")
    _add_masks_out(sp, "data/analysis/burgess_scan_1e9.json")
    sp.set_defaults(func=_cmd_census)

    sp = sub.add_parser(
        "scaled",
        help="regenerate burgess_scan_1e10_1e11.json (window samples "
             "10^9..10^11 + complete 10^11 deep tail)",
        description="Scaled ladder census: systematic window samples in "
                    "four half-decade bins 10^9..10^11 plus the COMPLETE "
                    "10^11 deep tail (R_min >= 43). Requires "
                    f"{_TAIL_1E11}. Reproduces "
                    "data/analysis/burgess_scan_1e10_1e11.json.")
    sp.add_argument("--workers", type=int, default=4,
                    help="multiprocessing workers (default: 4)")
    sp.add_argument("--windows", type=int, default=2500,
                    help="sample windows per half-decade bin "
                         "(default: 2500)")
    sp.add_argument("--per-window", type=int, default=4,
                    help="hard primes taken per window (default: 4)")
    sp.add_argument("--tail", default=_TAIL_1E11,
                    help=f"deep-tail dataset (default: {_TAIL_1E11})")
    sp.add_argument("--extend-cap", type=int, default=640,
                    help="extended rung cap for cap-400-unresolved tail "
                         "primes (default: 640)")
    sp.add_argument("--out",
                    default="data/analysis/burgess_scan_1e10_1e11.json",
                    help="output JSON path (default: "
                         "data/analysis/burgess_scan_1e10_1e11.json)")
    sp.set_defaults(func=_cmd_scaled)

    sp = sub.add_parser(
        "failures",
        help="regenerate burgess_failures_1e9.json "
             "(characterize_budget_failures)",
        description="Structural characterization of the selected-residual "
                    "failures below 10^9 (reach diagnostics, with a "
                    "matched success control group). Reproduces "
                    "data/analysis/burgess_failures_1e9.json.")
    _add_masks_out(sp, "data/analysis/burgess_failures_1e9.json")
    sp.set_defaults(func=_cmd_failures)

    sp = sub.add_parser(
        "proxy",
        help="regenerate burgess_proxy_1e9.json (proxy_ratio_scan)",
        description="Hypothesis-P proxy-ratio measurement at rungs 0/1 of "
                    "the selected ladder, on the 10^9 masks. Reproduces "
                    "data/analysis/burgess_proxy_1e9.json.")
    sp.add_argument("--sample-step", type=int, default=20,
                    help="prime subsampling step (default: 20)")
    _add_masks_out(sp, "data/analysis/burgess_proxy_1e9.json")
    sp.set_defaults(func=_cmd_proxy)

    sp = sub.add_parser(
        "proxy-scaled",
        help="regenerate burgess_proxy_scaled.json "
             "(proxy_ratio_scan_scaled)",
        description="Mask-free Hypothesis-P measurement over window "
                    "samples in four half-decade bins 10^9..10^11. "
                    "Reproduces data/analysis/burgess_proxy_scaled.json.")
    sp.add_argument("--workers", type=int, default=4,
                    help="multiprocessing workers (default: 4)")
    sp.add_argument("--windows", type=int, default=2500,
                    help="sample windows per half-decade bin "
                         "(default: 2500)")
    sp.add_argument("--per-window", type=int, default=4,
                    help="hard primes taken per window (default: 4)")
    sp.add_argument("--out", default="data/analysis/burgess_proxy_scaled.json",
                    help="output JSON path (default: "
                         "data/analysis/burgess_proxy_scaled.json)")
    sp.set_defaults(func=_cmd_proxy_scaled)

    sp = sub.add_parser(
        "admissibility",
        help="regenerate burgess_admissibility.json (Theorem 5.8 "
             "admissibility census of first rungs)",
        description="Census of the paper's Theorem 5.8 admissibility "
                    "conditions (A1)-(A3) over the hard primes below the "
                    "limit: how many first rungs pass (A1) alone, how "
                    "many have a NONEMPTY counted family, the 2-adic "
                    "case split, and how many have R0 prime. Reproduces "
                    "data/analysis/burgess_admissibility.json and "
                    "records its comparison against the figures quoted "
                    "in Remark 5.9.")
    sp.add_argument("--limit", type=int, default=2 * 10**7,
                    help="upper bound on hard primes (default: 2e7, the "
                         "range quoted in Remark 5.9)")
    sp.add_argument("--max-exemplars", type=int, default=50,
                    help="admissible first rungs recorded in full "
                         "(default: 50)")
    sp.add_argument("--out",
                    default="data/analysis/burgess_admissibility.json",
                    help="output JSON path (default: "
                         "data/analysis/burgess_admissibility.json)")
    sp.set_defaults(func=_cmd_admissibility)

    if argv is None:
        argv = sys.argv[1:]
    if not argv:  # historical behavior: bare invocation runs the census
        argv = ["census"]
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
