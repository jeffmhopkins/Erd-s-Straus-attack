#!/usr/bin/env python3
"""Branch enumeration for the residual-method failure model: maximal
failing supports and their two-sided window containers (Open Problem 2
ground truth; THEORY.md §2.11).

Model (cyclic, prime R ≡ 3 mod 4) — bit-compatible with
:func:`erdos_straus.theory.verify_support_bound`: d = R−1, ambient group
Z/d in discrete logs w.r.t. the primitive root chosen by
``theory._dlog_table``.  A configuration is a support S ⊆ Z/d ∖ {0} at
minimal multiplicities (budget e_v ∈ {0,1,2} per class — sanctioned by
the Lemma-4.1 monotonicity reduction) plus the p-class π ∈ Z/d with
budget f ∈ {0,1,2}.  Target t(π) = (d/2 + 2π + inv4log) mod d, exactly
the formula of the verified support-bound code.  Key reformulation used
throughout: with Reach₀(S) = {Σ e_v v : e_v ∈ {0,1,2}},

    S FAILS for π  ⟺  Reach₀(S) ∩ T(π) = ∅,   T(π) = {t, t−π, t−2π}.

Failure is downward-closed in S, so the whole failing family is
described by its antichain of MAXIMAL failing supports: failing S such
that S ∪ {w} succeeds for every w ∉ S ∪ {0}.  Enumeration is a memoized
DFS on (next-class, reach-mask); memoizing on masks collapses the
exponential subgroup families and is what makes R = 47–59 feasible.

Composite R: the same model in G = (Z/R)*, product sets ∏_{v∈S}{1,v,v²}
and target −4⁻¹π², mirroring ``theory.solvable_exact_general`` /
``theory.kneser_support_general`` (bit-compatible: for an involution
{1, v, v²} = {1, v}, exactly the cap min(2e, ord−1) at e = 1).

Container class (the classification that closes with zero unstructured
supports): TWO-SIDED coset progressions, a.k.a. window containers.  For
a kernel K ≤ Z/d (K = the h-element subgroup, h | d) with quotient map
φ_K : Z/d → Z/(d/h), a direction ū and a window [c̄, c̄+w−1] ∋ 0̄,

    C(K, W) = φ_K⁻¹({0̄} ∪ ū·[c̄, c̄+w−1]) ∖ {0}
            = (K + ū·{−k₁, …, k₂}) ∖ {0},   k₁ = −c̄, k₂ = c̄+w−1,

of size h·w − 1 nonzero classes.  :func:`min_window_container` finds the
exact minimum over all (K, ū, window); :func:`branch_census` checks the
CONTAINER LAW: every maximal failing support fits some C(K, W) with
|C(K, W)| ≤ d/2 − 1 (equality attained by the quadratic-residue /
Type-I branch).  Multiplicatively for composite R:
C = H·γ^[−k₁..k₂] ∖ {1} in (Z/R)*.

Validation heritage (scratchpad round; memo "branch_enumeration.md"):
the enumerator's T-mask predicate was checked pairwise against the
reach-bit predicate of ``theory.verify_support_bound`` on the full
size-d/2 census at R = 19 and 23 with zero disagreements
(:func:`census_crosscheck` reproduces that check); an unmemoized DFS
with a direct leaf maximality test reproduced the memoized output
exactly per π at R = 19, 23 (cyclic) and 15, 35, 39 (composite);
sampled supports were re-verified by raw e-vector reach enumeration;
and the two-sided minimal-container search was verified against
exhaustive (K, step, window) search.  Reference counts (archived in
``data/analysis/branch_maximal_supports.json``): 336 / 1,034 / 4,291 /
40,759 / 93,897 / 495,782 maximal supports at R = 19/23/31/43/47/59 and
16 / 1,124 / 1,124 at R = 15/35/39.

Runtime honesty (pure Python): R ≤ 31 takes seconds, R = 43 ≈ 1 min,
R = 47 ≈ 2–3 min, R = 59 ≈ 15–30 min for the enumeration plus a few
minutes of container classification over its 496k supports.  R = 67 is
out of reach of this implementation.  Composite R ∈ {15, 35, 39} are
fast (< 1 min).

CLI:  python -m erdos_straus.branch_enum census R [R ...]
refreshes the per-R entries of the consolidated archive
``data/analysis/branch_maximal_supports.json``.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from collections import Counter
from itertools import combinations
from typing import Callable, Dict, FrozenSet, List, Optional, Sequence, Tuple

from erdos_straus.theory import _dlog_table, unit_group


DEFAULT_ARCHIVE = "data/analysis/branch_maximal_supports.json"

Support = Tuple[int, ...]


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    k = 2
    while k * k <= n:
        if n % k == 0:
            return False
        k += 1
    return True


def _divisors(n: int) -> List[int]:
    return [k for k in range(1, n + 1) if n % k == 0]


# --- cyclic model (prime R): masks, targets, folding -----------------------

def model_params(R: int) -> Tuple[int, Dict[int, int], int]:
    """(d, discrete-log table, log 4⁻¹) for prime R — the exact coordinates
    of ``theory.verify_support_bound``."""
    d = R - 1
    _, LOG = _dlog_table(R)
    inv4_log = LOG[pow(4, -1, R)]
    return d, LOG, inv4_log


def make_fold(d: int) -> Tuple[Callable[[int, int], int], int]:
    """The reach-folding step over Z/d as bitmasks: fold(m, v) =
    m | rot(m, v) | rot(m, 2v) — adding budget-2 use of class v."""
    FULL = (1 << d) - 1

    def fold(m: int, v: int) -> int:
        r = m | (((m << v) | (m >> (d - v))) & FULL)
        v2 = (2 * v) % d
        if v2:
            r |= ((m << v2) | (m >> (d - v2))) & FULL
        return r

    return fold, FULL


def target_log(d: int, pi: int, inv4_log: int) -> int:
    """t(π) = log(−4⁻¹p²) = (d/2 + 2π + inv4log) mod d — the target
    formula of ``theory.verify_support_bound``, verbatim."""
    return (d // 2 + 2 * pi + inv4_log) % d


def target_mask(d: int, pi: int, t: int) -> int:
    """Bitmask of T(π) = {t, t−π, t−2π}: Reach₀(S) ∩ T(π) ≠ ∅ ⟺ the
    p-budgeted reach hits t."""
    m = 0
    for i in range(3):
        m |= 1 << ((t - i * pi) % d)
    return m


# --- maximal-failing enumeration (shared DFS core) -------------------------

def _maximal_failing(elems: Sequence[int], init_mask: int, Tm: int,
                     fold: Callable[[int, int], int]
                     ) -> Tuple[List[Tuple[Support, int]], int]:
    """All maximal failing supports over ``elems`` for target-mask Tm.

    Memoized DFS on (next-element index, reach-mask).  ``g(i, m)``
    returns the locally maximal completions from index i: final mask
    failing, and every excluded element blocked by the FINAL mask (fold
    is monotone in m, so an element blocked now is blocked forever).
    Returns ([(support, final mask), ...], number of memo states).
    """
    if init_mask & Tm:      # identity already succeeds: no failing supports
        return [], 0
    n = len(elems)
    memo: Dict[Tuple[int, int], Tuple] = {}

    def g(i: int, m: int) -> Tuple:
        if i == n:
            return ((m, ()),)
        key = (i, m)
        r = memo.get(key)
        if r is not None:
            return r
        v = elems[i]
        out = []
        nm = fold(m, v)
        if nm & Tm == 0:
            # include v
            for (mf, A) in g(i + 1, nm):
                out.append((mf, (v,) + A))
            # exclude v: only maximal if v is blocked by the final mask
            for (mf, A) in g(i + 1, m):
                if fold(mf, v) & Tm:
                    out.append((mf, A))
        else:
            # v auto-blocked forever
            out = list(g(i + 1, m))
        r = tuple(out)
        memo[key] = r
        return r

    res = [(A, mf) for (mf, A) in g(0, init_mask)]
    nstates = len(memo)
    memo.clear()
    return res, nstates


def verify_maximal(S: Sequence[int], d: int, Tm: int,
                   fold: Callable[[int, int], int]) -> Tuple[bool, str]:
    """Independent direct re-check that S is failing and maximal."""
    m = 1
    for v in S:
        m = fold(m, v)
    if m & Tm:
        return False, "not failing"
    Sset = set(S)
    for w in range(1, d):
        if w in Sset:
            continue
        if fold(m, w) & Tm == 0:
            return False, f"extendable by {w}"
    return True, "ok"


def maximal_failing_supports(R: int, pi: Optional[int] = None
                             ) -> Dict[int, List[Support]]:
    """Maximal failing supports for prime R, per p-class.

    Returns {π: sorted list of supports (tuples of discrete logs)} for
    every π ∈ Z/d, or for the single class when ``pi`` is given.  Every
    support is re-verified by the direct failing+maximality predicate.
    """
    if not _is_prime(R):
        raise ValueError(f"R={R} is not prime; use branch_census for "
                         "composite moduli")
    d, _, inv4_log = model_params(R)
    fold, _ = make_fold(d)
    out: Dict[int, List[Support]] = {}
    classes = [pi] if pi is not None else list(range(d))
    for p in classes:
        Tm = target_mask(d, p, target_log(d, p, inv4_log))
        res, _ = _maximal_failing(range(1, d), 1, Tm, fold)
        sups = sorted(tuple(A) for (A, _mf) in res)
        for S in sups:
            ok, msg = verify_maximal(S, d, Tm, fold)
            if not ok:
                raise AssertionError(f"R={R} pi={p} S={S}: {msg}")
        out[p] = sups
    return out


def census_crosscheck(R: int) -> Dict:
    """Predicate agreement with ``theory.verify_support_bound`` on the
    full size-d/2 support census (the exact object that function
    enumerates): for every support of size d/2 over the nonzero logs and
    every p-class, the T-mask failing predicate used by this module must
    equal the reach-bit predicate of the verified code, and the failure
    lists must coincide.  Feasible for R ≤ 23 (24,310 × 18 pairs at 19).
    """
    from erdos_straus.theory import verify_support_bound

    d, _, inv4_log = model_params(R)
    fold, FULL = make_fold(d)

    def rot(m: int, s: int) -> int:
        s %= d
        return ((m << s) | (m >> (d - s))) & FULL if s else m

    disagreements = 0
    my_failures = []
    n_pairs = 0
    for S in combinations(range(1, d), d // 2):
        base = 1
        for v in S:
            base = fold(base, v)
        for pi in range(d):
            t = target_log(d, pi, inv4_log)
            reach = base | rot(base, pi) | rot(base, 2 * pi)
            fail_theory = not (reach >> t) & 1
            fail_mine = base & target_mask(d, pi, t) == 0
            n_pairs += 1
            if fail_theory != fail_mine:
                disagreements += 1
            if fail_mine:
                my_failures.append((S, pi))
    ref = verify_support_bound(R)
    return {
        "R": R, "pairs": n_pairs, "disagreements": disagreements,
        "my_failures": len(my_failures),
        "ref_failures": len(ref["failures"]),
        "failure_lists_match":
            sorted(my_failures) == sorted(ref["failures"]),
        "lemma_holds": ref["lemma_holds"],
        "agree": disagreements == 0
            and sorted(my_failures) == sorted(ref["failures"]),
    }


# --- minimal two-sided window containers (cyclic) --------------------------

def min_window_container(S: Sequence[int], d: int
                         ) -> Optional[Tuple[int, int, int, int, int,
                                             FrozenSet[int]]]:
    """Minimal two-sided window container of S ⊆ Z/d ∖ {0}, exact search.

    Over every kernel order h | d (K = the (d/h)-multiples), direction
    step s in the quotient Z/m (m = d/h) and minimal cyclic window
    containing index 0 and the images of S, minimize the preimage size
    h·w.  Returns (size, h, s, k1, k2, container) where ``container`` is
    the frozenset K + s·[−k1, k2] INCLUDING 0 and size = h·w = |container|;
    the paper's window container C(K, W) = container ∖ {0} has size − 1
    nonzero classes (the quantity bounded by d/2 − 1 in the container
    law).  Returns None only if no proper (size < d) container exists —
    never observed for a failing support.
    """
    Sset = set(S)
    if not Sset:
        return (1, 1, 0, 0, 0, frozenset([0]))
    best = None
    for h in _divisors(d):
        if h == d:
            continue
        m = d // h
        I = {x % m for x in Sset}
        if I == {0}:                      # S inside the kernel itself
            if best is None or h < best[0]:
                cont = frozenset((j * m) % d for j in range(h))
                best = (h, h, 0, 0, 0, cont)
            continue
        for s in range(1, m):
            g = math.gcd(s, m)
            if any(x % g for x in I):
                continue
            o = m // g                    # order of s in Z/m
            sinv = pow(s // g, -1, o)     # solve e·s ≡ x (mod m)
            J = {0}
            for x in I:
                J.add((x // g) * sinv % o)
            pts = sorted(J)
            if len(pts) == o:
                arclen = o
            else:                         # minimal cyclic arc covering J
                maxgap = max((pts[(i + 1) % len(pts)] - pts[i]) % o
                             for i in range(len(pts)))
                arclen = o - maxgap + 1
            size = h * arclen
            if size >= d:
                continue
            if best is None or size < best[0]:
                gi = max(range(len(pts)),
                         key=lambda i: (pts[(i + 1) % len(pts)] - pts[i]) % o)
                start = pts[(gi + 1) % len(pts)]
                cont = frozenset((j * m + (start + e) * s) % d
                                 for j in range(h) for e in range(arclen))
                k1 = (0 - start) % o
                k2 = arclen - 1 - k1
                best = (size, h, s, k1, k2, cont)
    return best


def _window_label(best: Optional[Tuple], size_total: int) -> str:
    """Classification of a support from its minimal window container:
    'subgroup' (pure kernel, step 0), 'window' (density ≤ 0.9), else
    'unstructured' (never observed)."""
    if best is None:
        return "unstructured"
    size, _h, step = best[0], best[1], best[2]
    if step == 0:
        return "subgroup"
    if size <= 0.9 * size_total:
        return "window"
    return "unstructured"


def _subgroup_contained(S: Sequence[int], d: int) -> bool:
    """Anchored test (a): S inside a PROPER subgroup of Z/d (the index-m
    subgroup is the set of m-multiples, m | d, m > 1)."""
    if not S:
        return True
    return any(all(x % m == 0 for x in S)
               for m in _divisors(d) if m > 1)


# --- composite model: G = (Z/R)* -------------------------------------------

def group_data(R: int):
    """(G, g, index table, per-element transition masks) for (Z/R)*.
    TR[v][i] = bits contributed when element i is multiplied by
    {1, v, v²} (budget 2; = {1, v} for involutions, matching the
    min(2e, ord−1) cap of ``theory.solvable_exact_general`` at e = 1)."""
    G = unit_group(R)
    g = len(G)
    idx = {x: i for i, x in enumerate(G)}
    TR = {}
    for v in G:
        v2 = v * v % R
        TR[v] = [(1 << i) | (1 << idx[G[i] * v % R]) | (1 << idx[G[i] * v2 % R])
                 for i in range(g)]
    return G, g, idx, TR


def make_fold_units(TR: Dict[int, List[int]]) -> Callable[[int, int], int]:
    def fold(m: int, v: int) -> int:
        out = 0
        t = TR[v]
        mm = m
        while mm:
            b = mm & -mm
            out |= t[b.bit_length() - 1]
            mm ^= b
        return out
    return fold


def all_subgroups(G: Sequence[int], R: int) -> List[FrozenSet[int]]:
    """All subgroups of (Z/R)* by closure BFS, sorted by order."""
    def closure(gens):
        H = {1}
        frontier = {1}
        while frontier:
            new = set()
            for x in H:
                for y in gens:
                    z = x * y % R
                    if z not in H:
                        new.add(z)
            H |= new
            frontier = new
        return frozenset(H)

    subs = {frozenset([1])}
    frontier = {frozenset([1])}
    while frontier:
        new = set()
        for H in frontier:
            for v in G:
                H2 = closure(set(H) | {v})
                if H2 not in subs:
                    new.add(H2)
        subs |= new
        frontier = new
    return sorted(subs, key=len)


def min_window_container_units(S: Sequence[int], R: int,
                               subgroups: Optional[List[FrozenSet[int]]] = None
                               ) -> Optional[Tuple]:
    """Composite analogue of :func:`min_window_container` in G = (Z/R)*:
    minimal C = H·γ^[−k₁..k₂] (identity ∈ C) containing S.  Returns
    (size, H, gamma, arclen, container) with the identity INCLUDED in
    ``container`` and size = |container|; the window container of the
    law is container ∖ {1} with size − 1 elements."""
    G = unit_group(R)
    g = len(G)
    if subgroups is None:
        subgroups = all_subgroups(G, R)
    Sset = set(S)
    if not Sset:
        return (1, frozenset([1]), 1, 1, frozenset([1]))
    best = None
    for H in subgroups:
        h = len(H)
        if h == g:
            continue
        if Sset <= H:
            if best is None or h < best[0]:
                best = (h, H, 1, 1, frozenset(H))
            continue
        for gamma in G:
            if gamma == 1:
                continue
            o, x = 1, gamma            # order of gamma in G/H
            while x not in H:
                x = x * gamma % R
                o += 1
            pos: Dict[int, int] = {}
            c = 1
            for e in range(o):
                for hh in H:
                    y = c * hh % R
                    if y not in pos:
                        pos[y] = e
                c = c * gamma % R
            if not Sset <= pos.keys():
                continue
            J = {0} | {pos[s] for s in Sset}
            pts = sorted(J)
            if len(pts) == o:
                arclen, start = o, 0
            else:
                gaps = [(pts[(i + 1) % len(pts)] - pts[i]) % o
                        for i in range(len(pts))]
                gi = max(range(len(pts)), key=lambda i: gaps[i])
                arclen = o - gaps[gi] + 1
                start = pts[(gi + 1) % len(pts)]
            size = h * arclen
            if size >= g:
                continue
            if best is None or size < best[0]:
                cont = frozenset(pow(gamma, start + e, R) * hh % R
                                 for e in range(arclen) for hh in H)
                best = (size, H, gamma, arclen, cont)
    return best


def maximal_failing_supports_general(R: int, pi: Optional[int] = None
                                     ) -> Dict[int, List[Support]]:
    """Composite analogue of :func:`maximal_failing_supports` in
    G = (Z/R)*: {π (unit): sorted supports (tuples of units)}.  Target
    T(π) = {t·π⁻ⁱ : i = 0,1,2}, t = −4⁻¹π² — the class of −pa."""
    G, g, idx, TR = group_data(R)
    fold = make_fold_units(TR)
    init_mask = 1 << idx[1]
    inv4 = pow(4, -1, R)
    elems = [v for v in G if v != 1]
    out: Dict[int, List[Support]] = {}
    classes = [pi] if pi is not None else G
    for p in classes:
        t = (-inv4 * p * p) % R
        pinv = pow(p, -1, R)
        Tm = 0
        for i in range(3):
            Tm |= 1 << idx[t * pow(pinv, i, R) % R]
        res, _ = _maximal_failing(elems, init_mask, Tm, fold)
        sups = sorted(tuple(sorted(A)) for (A, _mf) in res)
        for S in sups:
            m = init_mask
            for v in S:
                m = fold(m, v)
            if m & Tm:
                raise AssertionError(f"R={R} pi={p} S={S}: not failing")
            for w in elems:
                if w not in S and fold(m, w) & Tm == 0:
                    raise AssertionError(
                        f"R={R} pi={p} S={S}: extendable by {w}")
        out[p] = sups
    return out


# --- the census ------------------------------------------------------------

def _summarize(R: int, kind: str, order: int, n_classes: int,
               n_pi_with_failures: int, sizes: Counter, labels: Counter,
               subgroup_contained: int, worst: int, n_at_bound: int,
               violations: List, containers: set, secs: float) -> Dict:
    n_max = sum(sizes.values())
    bound = order // 2 - 1
    return {
        "R": R,
        "kind": kind,
        "group_order": order,             # d = R−1 (cyclic) or φ(R)
        "n_p_classes": n_classes,
        "n_pi_with_failures": n_pi_with_failures,
        "n_maximal_supports": n_max,
        "support_sizes": {str(k): sizes[k] for k in sorted(sizes)},
        "min_support_size": min(sizes) if sizes else None,
        "max_support_size": max(sizes) if sizes else None,
        "kneser_bound": bound,            # Theorem S: |S| ≤ d/2 − 1
        "support_bound_ok": (max(sizes) <= bound) if sizes else True,
        "container_law": {
            "bound": bound,               # ⌊d/2⌋ − 1 nonzero classes
            "worst_min_container_size": worst,
            "n_at_bound": n_at_bound,
            "n_violations": len(violations),
            "violations": violations[:10],
            "verdict": "holds" if not violations else "violated",
        },
        "labels": {k: labels[k] for k in sorted(labels)},
        "subgroup_contained": subgroup_contained,
        "n_distinct_containers": len(containers),
        "secs": round(secs, 2),
    }


def branch_census(R: int, verbose: bool = False) -> Dict:
    """Full branch census at modulus R: enumerate every maximal failing
    support (all p-classes), compute each one's exact minimal window
    container, and check the container law |C| ≤ ⌊d/2⌋ − 1 (nonzero
    classes; d = R−1 for prime R, φ(R) for composite).  Returns the
    summary dict archived in ``data/analysis/branch_maximal_supports.json``.

    Runtime (pure Python): seconds for R ≤ 31, ≈ 1 min at 43, ≈ 3 min at
    47, ≈ 20–30 min at 59.
    """
    t0 = time.time()
    sizes: Counter = Counter()
    labels: Counter = Counter()
    containers: set = set()
    violations: List = []
    subgroup_contained = 0
    worst = -1
    n_at_bound = 0
    n_pi_fail = 0

    if _is_prime(R):
        d = R - 1
        bound = d // 2 - 1
        per_pi = maximal_failing_supports(R)
        for pi, sups in per_pi.items():
            if sups:
                n_pi_fail += 1
            for S in sups:
                sizes[len(S)] += 1
                if _subgroup_contained(S, d):
                    subgroup_contained += 1
                b = min_window_container(S, d)
                labels[_window_label(b, d)] += 1
                if b is None:
                    violations.append({"pi": pi, "support": list(S),
                                       "reason": "no proper container"})
                    continue
                nonzero = b[0] - 1
                worst = max(worst, nonzero)
                if nonzero == bound:
                    n_at_bound += 1
                elif nonzero > bound:
                    violations.append({"pi": pi, "support": list(S),
                                       "container_size": nonzero})
                containers.add(b[5])
            if verbose:
                print(f"  R={R} pi={pi:3d}: {len(sups):6d} maximal",
                      flush=True)
        return _summarize(R, "cyclic-prime", d, d, n_pi_fail, sizes,
                          labels, subgroup_contained, worst, n_at_bound,
                          violations, containers, time.time() - t0)

    # composite: G = (Z/R)*
    G = unit_group(R)
    g = len(G)
    bound = g // 2 - 1
    subgroups = all_subgroups(G, R)
    proper = [H for H in subgroups if len(H) < g]
    per_pi = maximal_failing_supports_general(R)
    for pi, sups in per_pi.items():
        if sups:
            n_pi_fail += 1
        for S in sups:
            sizes[len(S)] += 1
            if any(set(S) <= H for H in proper):
                subgroup_contained += 1
            b = min_window_container_units(S, R, subgroups)
            if b is None:
                labels["unstructured"] += 1
                violations.append({"pi": pi, "support": list(S),
                                   "reason": "no proper container"})
                continue
            size, H, _gamma, _arclen, cont = b
            if set(S) <= H:
                labels["subgroup"] += 1
            elif size <= 0.9 * g:
                labels["window"] += 1
            else:
                labels["unstructured"] += 1
            nonzero = size - 1
            worst = max(worst, nonzero)
            if nonzero == bound:
                n_at_bound += 1
            elif nonzero > bound:
                violations.append({"pi": pi, "support": list(S),
                                   "container_size": nonzero})
            containers.add(cont)
        if verbose:
            print(f"  R={R} pi={pi:3d}: {len(sups):6d} maximal", flush=True)
    return _summarize(R, "composite-abelian", g, g, n_pi_fail, sizes,
                      labels, subgroup_contained, worst, n_at_bound,
                      violations, containers, time.time() - t0)


# --- archive management & CLI ----------------------------------------------

def update_archive(path: str, entries: Dict[str, Dict]) -> Dict:
    """Merge per-R census entries into the consolidated archive JSON."""
    try:
        with open(path) as fh:
            archive = json.load(fh)
    except FileNotFoundError:
        archive = {
            "description":
                "Maximal failing supports of the residual-method failure "
                "model and their minimal two-sided window containers "
                "C(K, W), per modulus R (cyclic prime and composite "
                "abelian). Generated by erdos_straus.branch_enum.",
            "container_law":
                "Every maximal failing support fits a window container of "
                "at most floor(d/2) - 1 nonzero classes (d = R-1 for prime "
                "R, phi(R) for composite); equality is attained by the "
                "quadratic-residue (Type-I) branch.",
            "per_R": {},
        }
    archive["per_R"].update(entries)
    archive["per_R"] = {k: archive["per_R"][k]
                        for k in sorted(archive["per_R"], key=int)}
    with open(path, "w") as fh:
        json.dump(archive, fh, indent=1)
    return archive


def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("census", help="run the branch census for the given "
                       "moduli and refresh the archive")
    c.add_argument("R", type=int, nargs="+",
                   help="moduli (R ≡ 3 mod 4; prime or composite). "
                   "Runtime warning: R = 59 takes ~20-30 min pure-Python.")
    c.add_argument("--archive", default=DEFAULT_ARCHIVE)
    c.add_argument("--no-archive", action="store_true",
                   help="print the census without touching the archive")
    c.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args(argv)

    entries = {}
    for R in args.R:
        if R % 4 != 3:
            print(f"skipping R={R}: not ≡ 3 (mod 4)")
            continue
        res = branch_census(R, verbose=args.verbose)
        entries[str(R)] = res
        law = res["container_law"]
        print(f"R={R} ({res['kind']}, order {res['group_order']}): "
              f"{res['n_maximal_supports']} maximal supports, sizes "
              f"{res['min_support_size']}..{res['max_support_size']} "
              f"(Kneser bound {res['kneser_bound']}), container law "
              f"{law['verdict'].upper()} (worst {law['worst_min_container_size']}"
              f" vs bound {law['bound']}), "
              f"{res['n_distinct_containers']} distinct containers, "
              f"{res['secs']}s", flush=True)
    if entries and not args.no_archive:
        update_archive(args.archive, entries)
        print(f"archive updated: {args.archive}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
