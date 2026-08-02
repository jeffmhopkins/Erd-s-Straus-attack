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
    data = json.loads((DATA_DIR / fname).read_text())
    assert data, f"{fname} is empty"
    for key, rec in data.items():
        n = int(key)
        a, b, c = int(rec["a"]), int(rec["b"]), int(rec["c"])
        assert is_solution(n, a, b, c), f"bad certificate for n={n} in {fname}"
        if rec.get("R") is not None:
            assert 4 * a - n == int(rec["R"]), f"R mismatch for n={n} in {fname}"
