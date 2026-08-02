"""Erdős–Straus conjecture attack harness.

Utilities for searching, constructing, and verifying solutions to

    4/n = 1/a + 1/b + 1/c

with a focus on the hard-class primes (Mordell exceptional residues mod 840).

Public API
----------
solver
    Core utilities: `is_solution`, `hard_residue`, `generate_hard_primes`,
    classical identities and a brute-force search.
residual_solver
    The residual method R = 4a - n with sympy-based divisor factoring.
parametric_search
    Fixed-residual parametric experiments over the hard residue classes.
verify
    Independent verification of the JSON solution certificates in ``data/``.
"""

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
    minimal_R_stats,
)

__all__ = [
    "is_solution",
    "normalize",
    "hard_residue",
    "generate_hard_primes",
    "known_easy_solutions",
    "find_any_solution",
    "solve_residual",
    "find_solution_by_residuals",
    "minimal_R_stats",
]

__version__ = "0.1.0"
