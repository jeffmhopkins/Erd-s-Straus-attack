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
