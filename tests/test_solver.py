"""Tests for the core solver utilities and the residual engine."""

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


def test_find_any_solution_matches_brute_force_small():
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
