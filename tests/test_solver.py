"""Tests for the solver utilities, the residual engine, the
theory-layer finite checks, and the shipped certificate datasets."""

import json
from pathlib import Path

import pytest

from erdos_straus.solver import (
    is_solution,
    normalize,
    hard_residue,
    generate_hard_primes,
    known_easy_solutions,
    find_any_solution,
)
from erdos_straus.residual_solver import (
    solve_residual,
    find_solution_by_residuals,
)

DATA_DIR = Path(__file__).resolve().parents[1] / "data"


# --- is_solution -----------------------------------------------------------

def test_is_solution_accepts_known_identity():
    # 4/3 = 1/1 + 1/6 + 1/6
    assert is_solution(3, 1, 6, 6)


def test_is_solution_rejects_wrong():
    assert not is_solution(3, 1, 6, 7)


def test_is_solution_rejects_nonpositive():
    assert not is_solution(3, 0, 6, 6)
    assert not is_solution(3, 1, -6, 6)


def test_normalize_sorts():
    assert normalize(6, 1, 6) == (1, 6, 6)


# --- hard_residue ----------------------------------------------------------

@pytest.mark.parametrize("r", [1, 121, 169, 289, 361, 529])
def test_hard_residues(r):
    assert hard_residue(r)
    assert hard_residue(r + 840)


@pytest.mark.parametrize("r", [0, 2, 3, 4, 5, 11, 100, 120])
def test_non_hard_residues(r):
    assert not hard_residue(r)


def test_generate_hard_primes_are_prime_and_hard():
    primes = generate_hard_primes(20000)
    assert 1009 in primes  # 1009 % 840 == 169
    for p in primes:
        assert hard_residue(p)
    # all entries strictly increasing / unique
    assert primes == sorted(set(primes))


# --- classical identities --------------------------------------------------

@pytest.mark.parametrize("n", [7, 11, 19, 23, 31, 4 * 25 + 3])
def test_known_easy_solution_for_3_mod_4(n):
    assert n % 4 == 3
    sol = known_easy_solutions(n)
    assert sol is not None
    assert is_solution(n, *sol)


# --- residual solver -------------------------------------------------------

def test_solve_residual_recovers_valid_triple():
    # 1009 is a hard prime; known certificate has R=3.
    sol = solve_residual(1009, 3)
    assert sol is not None
    a, b, c = sol
    assert is_solution(1009, a, b, c)


def test_find_solution_by_residuals_small_hard_primes():
    for p in generate_hard_primes(5000):
        res = find_solution_by_residuals(p, max_R=200)
        assert res is not None, f"no residual solution found for hard prime {p}"
        a, b, c, R = res
        assert is_solution(p, a, b, c)
        assert 4 * a - p == R


def test_find_any_solution_returns_valid_triple():
    for n in [5, 6, 7, 9, 13]:
        sol = find_any_solution(n, max_a_factor=5.0)
        assert sol is not None
        assert is_solution(n, *sol)


# --- certificate data files ------------------------------------------------

@pytest.mark.parametrize(
    "fname",
    [
        "hard_primes_2e5_solutions.json",
        "hard_primes_1e6_solutions.json",
        "high_R_primes_5e6.json",
    ],
)
def test_certificate_files_are_valid(fname):
    """Every stored (a, b, c) must exactly satisfy the equation."""
    from erdos_straus.verify import load_solutions

    data = load_solutions(DATA_DIR / fname)
    assert data, f"{fname} is empty"
    for key, rec in data.items():
        n = int(key)
        a, b, c = int(rec["a"]), int(rec["b"]), int(rec["c"])
        assert is_solution(n, a, b, c), f"bad certificate for n={n} in {fname}"
        if rec.get("R") is not None:
            assert 4 * a - n == int(rec["R"]), f"R mismatch for n={n} in {fname}"


def test_large_gz_dataset_sampled():
    """Spot-check the large gzipped 1.2e8 dataset (every 500th entry)."""
    from erdos_straus.verify import load_solutions

    path = DATA_DIR / "hard_primes_1.2e8_solutions.json.gz"
    data = load_solutions(path)
    assert len(data) > 200_000
    items = list(data.items())
    for key, rec in items[::500]:
        n = int(key)
        assert hard_residue(n)
        assert is_solution(n, int(rec["a"]), int(rec["b"]), int(rec["c"]))
        assert 4 * int(rec["a"]) - n == int(rec["R"])


def test_segmented_sieve_matches_monolithic():
    from erdos_straus.bulk_generate import (
        hard_primes_upto,
        hard_primes_upto_segmented,
    )

    mono = hard_primes_upto(300_000)
    seg = hard_primes_upto_segmented(300_000, segment_size=1 << 14)
    assert mono == seg


def test_rmap_dataset_reconstructs():
    """Sampled check: every stored minimal R reconstructs to a valid triple
    and no smaller admissible R works (i.e. R really is minimal)."""
    from erdos_straus.bulk_generate import (
        _init_small_primes,
        solve_residual as fast_solve,
    )
    from erdos_straus.verify import load_solutions

    _init_small_primes()
    path = DATA_DIR / "hard_primes_1e9_minimalR.json.gz"
    data = load_solutions(path)
    assert len(data) > 1_500_000
    items = list(data.items())
    for key, R in items[::5000]:
        n = int(key)
        assert hard_residue(n)
        sol = fast_solve(n, int(R))
        assert sol is not None, f"R={R} fails to reconstruct for n={n}"
        assert is_solution(n, *sol)
        for smaller in range(3, int(R), 4):
            assert fast_solve(n, smaller) is None, (
                f"n={n}: stored R={R} not minimal, R={smaller} works"
            )


def test_jacobi_symbol():
    from erdos_straus.theory import jacobi

    # squares are residues
    assert jacobi(4, 7) == 1 and jacobi(2, 7) == 1
    # -1 is a non-residue mod primes ≡ 3 (mod 4)
    for r in [3, 7, 11, 19, 23]:
        assert jacobi(r - 1, r) == -1
    # multiplicativity spot check
    assert jacobi(3, 7) * jacobi(5, 7) == jacobi(15, 7)


def test_theorem_A_R3_criterion_matches_solver():
    """Theorem A: R=3 works iff (p+3)/4 has a prime factor ≡ 2 (mod 3)."""
    from erdos_straus.bulk_generate import (
        _init_small_primes, factorize, solve_residual,
    )
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    for p in generate_hard_primes(200000):
        a = (p + 3) // 4
        pred = any(q % 3 == 2 for q in factorize(a))
        assert pred == (solve_residual(p, 3) is not None), p


def test_theorem_Aprime_R7_finite_verification():
    """Theorem A': the finite case analysis for R=7 has no violations."""
    from erdos_straus.theory import verify_R7_finite

    res = verify_R7_finite()
    assert res["theorem_holds"], res["violations"][:3]
    assert res["checked"] == 1536


def test_character_obstruction_prop1():
    """Prop 1: all-QR factor classes mod r|R (r≡3 mod 4) forces failure."""
    from erdos_straus.bulk_generate import (
        _init_small_primes, factorize, solve_residual,
    )
    from erdos_straus.theory import jacobi, obstruction_primes_of_R
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    checked = 0
    for p in generate_hard_primes(100000):
        for R in [7, 11, 19, 23]:
            a = (p + R) // 4
            qs = set(factorize(a)) | {p}
            for r in obstruction_primes_of_R(R):
                if all(jacobi(q, r) == 1 for q in qs):
                    assert solve_residual(p, R) is None, (p, R)
                    checked += 1
    assert checked > 10  # the obstruction does occur in range


def test_meta_theorem_solvable_exact_matches_solver():
    """solvable_exact (class-based criterion) agrees with the divisor
    search for R in {11, 19, 23} on small hard primes."""
    from erdos_straus.bulk_generate import _init_small_primes, solve_residual
    from erdos_straus.theory import solvable_exact
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    for p in generate_hard_primes(150000):
        for R in [11, 19, 23]:
            assert solvable_exact(p, R) == (
                solve_residual(p, R) is not None), (p, R)


def test_theorem_Adoubleprime_R11_dp_states():
    """The R=11 DP enumeration finds exactly the published state tally:
    16 success, 6 character-obstructed, 3 budget-limited, 0 subgroup."""
    from erdos_straus.theory import finite_criterion_dp, _dlog_table

    _, L11 = _dlog_table(11)
    r = finite_criterion_dp(11, forced_logs=[L11[3]])
    assert r["tally"] == {"success": 16, "fail_all_even": 6,
                          "fail_budget": 3}


def test_R7_dp_reproduces_theorem_Aprime():
    """The generic DP at R=7 reproduces Theorem A': no budget or subgroup
    failures - only the character dichotomy."""
    from erdos_straus.theory import finite_criterion_dp, _dlog_table

    _, L7 = _dlog_table(7)
    r = finite_criterion_dp(7, forced_logs=[L7[2]], p_res_set=[1, 2, 4])
    assert set(r["tally"]) == {"success", "fail_all_even"}


def test_support_bound_lemma_R19_R23():
    """Lemma S: no failing configuration at R=19 or R=23 has d/2 or more
    nonzero support classes (the sieve input for Theorems G and G')."""
    from erdos_straus.theory import verify_support_bound

    for R in [19, 23]:
        res = verify_support_bound(R)
        assert res["lemma_holds"], (R, res["failures"][:3])


def test_support_bound_dp_holds_through_R43():
    """The DP verifier confirms the support bound and extends the
    lemma to larger residuals (Theorem H chain)."""
    from erdos_straus.theory import verify_support_bound_dp

    for R in [19, 23, 31, 43]:
        res = verify_support_bound_dp(R)
        assert res["status"] == "OK" and res["lemma_holds"], (R, res)


def test_theorem_Atriple_R15_finite_enumeration():
    """Theorem A''' (R=15): the exhaustive configuration enumeration has
    no violations — success iff a Jacobi non-residue factor class occurs,
    with zero budget failures (the consistency relation kills them)."""
    from erdos_straus.theory import verify_R15_finite

    r = verify_R15_finite()
    assert r["theorem_holds"], r["violations"][:3]
    assert r["configs"] == 349_920
    assert r["fail"] == 540 and r["fail_with_nonresidue"] == 0


def test_theorem_Atriple_R15_criterion_matches_solver():
    """Theorem A''': R=15 works iff (p+15)/4 has a prime factor
    ≡ 7, 11, 13, 14 (mod 15) — i.e. with Jacobi (q|15) = −1."""
    from erdos_straus.bulk_generate import _init_small_primes, solve_residual
    from erdos_straus.theory import criterion_R15
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    for p in generate_hard_primes(200000):
        assert criterion_R15(p) == (solve_residual(p, 15) is not None), p


def test_solvable_exact_general_composites_match_solver():
    """The general (composite-R) exact engine agrees with the divisor
    search on the first composite residuals."""
    from erdos_straus.bulk_generate import _init_small_primes, solve_residual
    from erdos_straus.theory import solvable_exact_general
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    for p in generate_hard_primes(60000):
        for R in [15, 27, 35, 39]:
            assert solvable_exact_general(p, R) == (
                solve_residual(p, R) is not None), (p, R)


def test_solvable_exact_general_agrees_with_prime_engine():
    """On prime R the general engine reduces to the cyclic one."""
    from erdos_straus.bulk_generate import _init_small_primes
    from erdos_straus.theory import solvable_exact, solvable_exact_general
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    for p in generate_hard_primes(60000):
        for R in [11, 19]:
            assert solvable_exact_general(p, R) == solvable_exact(p, R), (p, R)


def test_kneser_strong_support_bound_cyclic():
    """Theorem S (Kneser): the maximum support of a non-full subset-sum
    mask in Z/(R-1) is exactly (R-3)/2 — the strong form of Lemma S."""
    from erdos_straus.theory import verify_support_bound_strong

    for R in [19, 23, 31]:
        r = verify_support_bound_strong(R)
        assert r["status"] == "OK" and r["strong_holds"], r
        assert r["max_nonfull_support"] == (R - 3) // 2


def test_kneser_support_bound_general_abelian():
    """The general-abelian (composite R) support bound: failure forbids
    at least half of the phi(R) unit classes."""
    from erdos_straus.theory import kneser_support_general

    for R in [15, 27, 35]:
        r = kneser_support_general(R)
        assert r["holds"] and r["half_forbidden"], r
        assert r["max_nonfull_support"] == r["g"] // 2 - 1


def test_reciprocity_structure_theorem():
    """Theorem J: (q|R) = (p|q) for odd primes q | (p+R)/4, R prime."""
    from erdos_straus.bulk_generate import _init_small_primes, factorize
    from erdos_straus.theory import jacobi
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    checked = 0
    for p in generate_hard_primes(50000):
        for R in [3, 7, 11, 19, 23, 31]:
            a = (p + R) // 4
            for q in factorize(a):
                if q % 2 == 1 and q != R:
                    assert jacobi(q, R) == jacobi(p, q), (p, R, q)
                    checked += 1
        # hard classes are squares mod 840 => p is a QR mod 3, 5, 7
        for small in [3, 5, 7]:
            assert jacobi(p, small) == 1, (p, small)
    assert checked > 100


def test_aggregate_identity_families():
    """Aggregate identity families (paper Prop. 1.12): p+1 / p+4 divisor identities give valid certificates,
    and the certificate's R genuinely divides p+1 or p+4."""
    from erdos_straus.theory import aggregate_identity_certificate
    from erdos_straus.solver import generate_hard_primes

    covered = 0
    for p in generate_hard_primes(100000):
        res = aggregate_identity_certificate(p)
        if res is not None:
            R, a, b, c = res
            assert R % 4 == 3
            assert (p + 1) % R == 0 or (p + 4) % R == 0
            assert is_solution(p, a, b, c)
            covered += 1
    assert covered > 0


def test_bulk_generate_matches_stored_minimal_R():
    """The fast bulk solver reproduces the minimal R of stored certificates."""
    from erdos_straus.bulk_generate import _init_small_primes, minimal_certificate
    from erdos_straus.verify import load_solutions

    _init_small_primes()
    data = load_solutions(DATA_DIR / "hard_primes_1e6_solutions.json")
    for key, rec in list(data.items())[::50]:
        n = int(key)
        res = minimal_certificate(n)
        assert res is not None
        a, b, c, R = res
        assert is_solution(n, a, b, c)
        assert R == rec["R"]


def test_burgess_selected_residual_reciprocity():
    """Burgess-route invariants (THEORY.md §2.10): for hard p, the least
    Legendre non-residue q is >= 11 (hard primes are QRs mod 3, 5, 7), the
    selected residual R = -p mod 4q is admissible with q | (p+R)/4, and the
    composite Jacobi reciprocity (q|R) = (p|q) = -1 holds at it."""
    from erdos_straus.bulk_generate import _init_small_primes
    from erdos_straus.burgess_scan import (least_legendre_nonresidue,
                                           selected_residual)
    from erdos_straus.solver import generate_hard_primes
    from erdos_straus.theory import jacobi

    _init_small_primes()
    for p in generate_hard_primes(100000):
        q = least_legendre_nonresidue(p)
        assert q is not None and q >= 11, (p, q)
        assert jacobi(p % q, q) == -1
        R = selected_residual(p, q)
        assert R % 4 == 3 and (p + R) % (4 * q) == 0
        assert jacobi(q % R, R) == -1, (p, q, R)


def test_reach_diagnostics_known_budget_failure():
    """Failure anatomy (THEORY.md 2.10): p = 3361 at its selected residual
    R = 27 is a true budget failure whose reach misses only the target."""
    from erdos_straus.bulk_generate import _init_small_primes
    from erdos_straus.burgess_scan import reach_diagnostics

    _init_small_primes()
    d = reach_diagnostics(3361, 27)
    assert not d["target_reached"]
    assert d["true_budget"] and not d["subgroup_miss"]
    assert d["missed"] == 1 and d["support_size"] <= 5


def test_prop22_contrapositive_on_selected_rung_failures():
    """Theorem B1's mechanism (THEORY.md 2.10): a selected-rung failure
    cannot have any prime factor of (p+R)/4 in the Prop 2.2 classes
    {t, t/p, t/p^2} mod R -- checked against ground truth solvability."""
    from erdos_straus.bulk_generate import (_init_small_primes,
                                            solve_residual, factorize)
    from erdos_straus.burgess_scan import (least_legendre_nonresidue,
                                           selected_residual)
    from erdos_straus.solver import generate_hard_primes

    _init_small_primes()
    checked = 0
    for p in generate_hard_primes(300000):
        q = least_legendre_nonresidue(p)
        R = selected_residual(p, q)
        if solve_residual(p, R) is not None:
            continue
        checked += 1
        t = (-pow(4, -1, R) * p * p) % R
        pinv = pow(p, -1, R)
        classes = {t, t * pinv % R, t * pinv * pinv % R}
        a = (p + R) // 4
        assert not any(u % R in classes for u in factorize(a)), (p, q, R)
    assert checked > 5


def test_branch_enum_R19_count_and_predicate_agreement():
    """Branch enumeration (THEORY.md 2.12): the migrated enumerator finds
    exactly the 336 maximal failing supports at R = 19, and its T-mask
    failing predicate agrees with theory.verify_support_bound's reach-bit
    predicate on the full size-9 census (24,310 supports x 18 p-classes)."""
    from erdos_straus.branch_enum import (census_crosscheck,
                                          maximal_failing_supports)

    per_pi = maximal_failing_supports(19)
    assert sum(len(v) for v in per_pi.values()) == 336
    # exactly one p-class (the one with 0 in T(pi)) has no failing supports
    assert sum(1 for v in per_pi.values() if not v) == 1

    chk = census_crosscheck(19)
    assert chk["agree"], chk
    assert chk["pairs"] == 437_580 and chk["disagreements"] == 0
    assert chk["failure_lists_match"] and chk["lemma_holds"]


def test_branch_enum_container_law_R19():
    """Container law at R = 19: every maximal failing support fits a
    two-sided window container C(K, W) of at most d/2 - 1 = 8 nonzero
    classes, with equality attained (the quadratic-residue branch)."""
    from erdos_straus.branch_enum import branch_census

    c = branch_census(19)
    assert c["n_maximal_supports"] == 336
    assert c["support_bound_ok"]  # Theorem S: |S| <= d/2 - 1
    law = c["container_law"]
    assert law["verdict"] == "holds" and law["n_violations"] == 0
    assert law["bound"] == 8
    assert law["worst_min_container_size"] == 8 and law["n_at_bound"] == 9
    assert c["labels"] == {"window": 336}  # zero unstructured supports


def test_branch_supports_archive_verdicts():
    """The consolidated branch archive parses, covers all nine enumerated
    moduli, and every per-R container-law verdict is "holds" with the
    Kneser support bound respected."""
    path = DATA_DIR / "analysis" / "branch_maximal_supports.json"
    with open(path) as fh:
        archive = json.load(fh)
    per_R = archive["per_R"]
    assert set(per_R) == {"15", "19", "23", "31", "35", "39",
                          "43", "47", "59"}
    for key, e in per_R.items():
        assert e["R"] == int(key)
        law = e["container_law"]
        assert law["verdict"] == "holds", key
        assert law["n_violations"] == 0 and not law["violations"]
        assert law["worst_min_container_size"] <= law["bound"]
        assert e["support_bound_ok"]
        assert e["max_support_size"] <= e["kneser_bound"]
        assert sum(e["support_sizes"].values()) == e["n_maximal_supports"]
    # spot-check the headline counts against the enumeration memo
    assert per_R["19"]["n_maximal_supports"] == 336
    assert per_R["59"]["n_maximal_supports"] == 495_782
    assert per_R["35"]["n_maximal_supports"] == 1_124


HARD_CLASSES = {1, 121, 169, 289, 361, 529}


def _reduced_forms(D):
    """All reduced primitive positive-definite forms (A, B, C) of
    discriminant D = B^2 - 4AC < 0."""
    from math import gcd, isqrt

    forms = []
    for A in range(1, isqrt(abs(D) // 3) + 1):
        for B in range(-A + 1, A + 1):
            if (B * B - D) % (4 * A):
                continue
            C = (B * B - D) // (4 * A)
            if C < A or (B < 0 and (A == C or A == -B)):
                continue
            if gcd(gcd(A, B), C) == 1:
                forms.append((A, B, C))
    return forms


def _primitively_represented_up_to(D, N):
    """{n <= N : n = f(x,y) for some reduced form f of discriminant D and
    some coprime (x, y)} -- i.e. n primitively represented by the (single,
    since D is a prime discriminant) genus of discriminant D."""
    from math import gcd, isqrt

    reps = set()
    for (A, B, C) in _reduced_forms(D):
        ymax = isqrt(4 * A * N // abs(D)) + 1
        halfwidth = isqrt(N // A) + 1
        for y in range(-ymax, ymax + 1):
            centre = -(B * y) // (2 * A)
            for x in range(centre - halfwidth, centre + halfwidth + 1):
                v = A * x * x + B * x * y + C * y * y
                if 0 < v <= N and gcd(x, y) == 1:
                    reps.add(v)
    return reps


def test_norm_form_bridge_equivalence():
    """The norm-form bridge, paper eq. (5.1) / THEORY.md 2.10: for a prime
    r = 3 (mod 4) and r not dividing n,

        every prime factor of n is a QR mod r
          <=>  -r is a square mod 4n
          <=>  n is PRIMITIVELY represented by a binary quadratic form of
               discriminant -r.

    Checked here on the shifted values a = (p+r)/4 of hard primes, for
    r = 3, 7, 11 (class number 1) and r = 23 (class number 3 -- the whole
    class group participates, since a prime discriminant has one genus)."""
    from sympy import primerange
    from sympy.ntheory.residue_ntheory import sqrt_mod

    from erdos_straus.bulk_generate import _init_small_primes, factorize
    from erdos_straus.theory import jacobi

    _init_small_primes()
    N = 20_000
    class_numbers = {3: 1, 7: 1, 11: 1, 23: 3}
    for r, h in class_numbers.items():
        assert r % 4 == 3
        forms = _reduced_forms(-r)
        assert len(forms) == h, (r, forms)
        reps = _primitively_represented_up_to(-r, N)
        tested = 0
        for p in primerange(5, 4 * N):
            if p % 840 not in HARD_CLASSES or (p + r) % 4:
                continue
            a = (p + r) // 4
            if a > N or a % r == 0:
                continue
            tested += 1
            all_qr = all(jacobi(u % r, r) == 1 for u in factorize(a))
            assert all_qr == (sqrt_mod(-r, 4 * a) is not None), (r, p, a)
            assert all_qr == (a in reps), (r, p, a)
        assert tested > 100, (r, tested)


def test_type_I_failure_family_exemplar_is_admissible():
    """Theorem 5.8's mechanism (THEORY.md 2.10; the corrected form of the
    old "Theorem P1"): p = 5,544,361 is in the Type-I failure family of its
    selected ladder -- R0 = 51 with r1 = 3, every prime factor of
    a = (p+R0)/4 a QR mod 3 -- and therefore provably fails R0 (Prop 2.1 at
    r1).  Its class is admissible in the CORRECTED sense: (A1) (q|r1) = +1;
    (A2) (l|r1) = +1 for every prime l <= q that the class forces to divide
    a (here only l = q = 31 -- this clause was missing from the printed
    Theorem P1 and its omission made that statement false); (A3) the 2-adic
    case r1 = 3 (mod 8) with a odd."""
    from sympy import primerange

    from erdos_straus.bulk_generate import (_init_small_primes, factorize,
                                            solve_residual)
    from erdos_straus.burgess_scan import (least_legendre_nonresidue,
                                           selected_residual)
    from erdos_straus.theory import jacobi

    _init_small_primes()
    p = 5544361
    q = least_legendre_nonresidue(p)
    R = selected_residual(p, q)
    assert (q, R) == (31, 51)
    r1 = 3
    assert R % r1 == 0 and r1 % 4 == 3
    a = (p + R) // 4
    fa = factorize(a)
    assert fa == {31: 1, 61: 1, 733: 1}
    assert all(jacobi(u % r1, r1) == 1 for u in fa)
    # (A1)
    assert jacobi(q % r1, r1) == 1
    # (A2): the class fixes a modulo every prime <= q, so the forced
    # divisors are a property of the class; each must be a QR mod r1.
    forced = [ell for ell in primerange(2, q + 1) if a % ell == 0]
    assert forced == [31]
    assert all(jacobi(ell % r1, r1) == 1 for ell in forced)
    # (A3): case A -- r1 = 3 (mod 8) and a odd.
    assert r1 % 8 == 3 and a % 2 == 1
    assert solve_residual(p, R) is None


def test_type_I_admissibility_vacuity_counterexample():
    """Why the printed "Theorem P1" was false (paper Remark 5.9): the old
    admissibility test asked only for (q|r1) = +1 plus a 2-adic clause, but
    the congruence class also forces small primes to divide a.  For q = 23,
    R0 = 35, r1 = 7 the old test passes -- (23|7) = +1, and R0 = 3 (mod 8)
    with p = 1 (mod 8) makes a odd, so the 2-adic clause is vacuous -- yet
    every hard prime has p = 1 (mod 3) while 35 = 2 (mod 3), so 3 | a
    always, and (3|7) = -1.  The counted family is EMPTY on every such
    class, against a claimed >> x/(log x)^{3/2}."""
    from erdos_straus.bulk_generate import _init_small_primes, factorize
    from erdos_straus.burgess_scan import (least_legendre_nonresidue,
                                           selected_residual)
    from erdos_straus.theory import jacobi

    _init_small_primes()
    q, R0, r1 = 23, 35, 7
    # the old test passes: (A1) holds and the 2-adic clause is vacuous
    assert R0 % 4 == 3 and r1 % 4 == 3 and R0 % r1 == 0
    assert jacobi(q % r1, r1) == 1
    assert R0 % 8 == 3          # with p = 1 (mod 8) this forces a odd
    # but (A2) fails at the forced divisor 3
    assert R0 % 3 == 2          # and hard primes have p = 1 (mod 3)
    assert jacobi(3, r1) == -1
    exemplars = [320401, 499801, 712321, 742681, 830449,
                 893929, 1035241, 1109761]
    for p in exemplars:
        assert p % 840 in HARD_CLASSES
        assert least_legendre_nonresidue(p) == q
        assert selected_residual(p, q) == R0
        a = (p + R0) // 4
        assert a % 2 == 1 and a % 3 == 0
        # so a always has a prime factor that is a non-residue mod r1:
        assert not all(jacobi(u % r1, r1) == 1 for u in factorize(a))


def test_admissibility_predicate_detects_class_forced_vacuity():
    """The vacuity mechanism of Remark 5.9 as reported by the shipped
    predicate (the test above checks the same arithmetic by hand; this one
    checks that burgess_scan.admissibility actually implements it).  For
    q = 23, R0 = 35 the only r1 = 3 (mod 4) candidate is 7; it passes (A1)
    and its 2-adic clause is vacuous (a odd), yet the CLASS forces 3 | a
    and (3|7) = -1, so (A2) fails and the counted family is empty.  The
    forcing is a property of the class, not of the sample prime: 3 is
    reported as forced because p = -R0 (mod 3) holds for every hard prime
    (p = 1 mod 3, 35 = 2 mod 3), and M = 840*11*13*17*19*23 is divisible
    by 3, so the residue is fixed across the class."""
    from erdos_straus.bulk_generate import _init_small_primes
    from erdos_straus.burgess_scan import (admissibility, class_modulus,
                                           forced_small_primes)

    _init_small_primes()
    q, R0, r1 = 23, 35, 7
    M = class_modulus(q)
    assert M == 840 * 11 * 13 * 17 * 19 * 23
    assert M % 3 == 0            # the class fixes p mod 3 -> 3 is decidable
    for p in [320401, 499801, 712321, 742681, 830449, 1109761]:
        rec = admissibility(p)
        assert (rec["q"], rec["R0"]) == (q, R0)
        assert rec["M"] == M
        # 3 and q = 23 are forced for the whole class; 3 is the killer.
        forced = forced_small_primes(p, R0, q)
        assert rec["forced_small_primes"] == forced
        assert 3 in forced and q in forced and 2 not in forced
        assert forced == [ell for ell in [2, 3, 5, 7, 11, 13, 17, 19, 23]
                          if rec["a"] % ell == 0]
        (cand,) = rec["r1_candidates"]     # 5 is 1 mod 4, so only r1 = 7
        assert cand["r1"] == r1
        assert cand["A1"] is True          # (23|7) = +1
        assert cand["two_adic_ok"] is True  # a odd: ell = 2 says nothing
        assert cand["A2"] is False and 3 in cand["A2_violations"]
        assert cand["nonempty"] is False
        # (A1) alone counts this rung; the corrected predicate does not.
        assert rec["A1"] is True
        assert rec["nonempty_family"] is False
        assert rec["a3_as_printed"] is False
        assert rec["selected_r1"] is None


def test_burgess_admissibility_archive_headline_counts():
    """The Theorem 5.8 availability census (Remark 5.9): among the 39,391
    hard primes below 2e7, 2,593 first rungs (6.6%) pass (A1) alone but
    only 9 (0.023%) have a NONEMPTY family under (A1)-(A3), split 5 case A
    / 0 case B / 4 mixed.  The archive also records the one figure that
    does NOT reproduce: R0 is prime for 65.2% of first rungs, not the
    93.4% quoted -- 93.4% = 100% - 6.6% is the share with no r1 passing
    (A1) at all, of which prime R0 is a strict subset."""
    path = DATA_DIR / "analysis" / "burgess_admissibility.json"
    with open(path) as fh:
        archive = json.load(fh)
    assert archive["limit"] == 20_000_000
    assert archive["hard_primes"] == 39_391
    c = archive["counts"]
    assert c["A1_only"] == 2_593
    assert round(c["A1_only_share"], 3) == 0.066
    assert c["nonempty_family"] == 9
    assert round(100 * c["nonempty_family_share"], 3) == 0.023
    assert c["case_split"] == {"A": 5, "B": 0, "mixed": 4}
    # (A3) exactly as printed keeps only cases A and B.
    assert c["a3_as_printed"] == 5
    assert c["primes_with_two_nonempty_r1"] == 0
    assert c["distinct_admissible_classes_q_R0_r1"] == 4
    # The corrected reading is a 285-fold thinning of the old statistic.
    assert c["A1_only"] > 280 * c["nonempty_family"]
    # R0 prime is never admissible, and is NOT the 93.4% class.
    assert c["R0_prime"] == 25_700
    assert round(c["R0_prime_share"], 3) == 0.652
    assert c["no_r1_candidate_passing_A1"] == 39_391 - 2_593
    assert round(c["no_r1_candidate_passing_A1_share"], 3) == 0.934
    assert c["R0_prime"] < c["no_r1_candidate_passing_A1"]
    checks = archive["paper_comparison"]["checks"]
    assert checks["R0_prime_share"]["agrees"] is False
    assert all(v["agrees"] for k, v in checks.items()
               if k != "R0_prime_share")
    # the two exemplars named in THEORY.md 2.10
    ex = {e["p"]: e for e in archive["exemplars"]}
    assert ex[5_544_361]["case"] == "A"
    assert (ex[5_544_361]["q"], ex[5_544_361]["R0"],
            ex[5_544_361]["r1"]) == (31, 51, 3)
    assert ex[5_505_361]["case"] == "mixed"
    assert (ex[5_505_361]["q"], ex[5_505_361]["R0"],
            ex[5_505_361]["r1"]) == (37, 91, 7)
    assert set(archive["definitions"]) >= {"forced", "A1", "A2",
                                           "A3_as_printed",
                                           "nonempty_family"}
