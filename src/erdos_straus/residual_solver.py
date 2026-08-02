#!/usr/bin/env python3
"""
Efficient residual-based solver for Erdős–Straus using divisor method.
This is the core of the attack harness for moderate n (up to ~10^6 easily, larger with care).
"""

import sympy as sp
from typing import Optional, Tuple, List
from fractions import Fraction

def is_solution(n: int, a: int, b: int, c: int) -> bool:
    return a > 0 and b > 0 and c > 0 and 4 * a * b * c == n * (b * c + a * c + a * b)

def solve_residual(n: int, R: int) -> Optional[Tuple[int, int, int]]:
    """Solve for given residual R = 4a - n > 0, a = (n + R)//4 integer."""
    if R <= 0 or (n + R) % 4 != 0:
        return None
    a = (n + R) // 4
    m = n * a
    d = R
    M2 = m * m
    try:
        # sympy.divisors is efficient for numbers with not too many factors
        divs = sp.divisors(M2)
        for k in divs:
            if (k + m) % d == 0:
                b = (k + m) // d
                if b >= 1:
                    ck = M2 // k
                    if (ck + m) % d == 0:
                        c = (ck + m) // d
                        if c >= b and is_solution(n, a, b, c):
                            return (a, b, c)
    except Exception:
        return None
    return None

def find_solution_by_residuals(n: int, max_R: int = 200) -> Optional[Tuple[int, int, int, int]]:
    """Try increasing residuals R ≡ -n (mod 4) (odd R for the odd n of interest) until a solution is found. Returns (a,b,c,R) or None."""
    # R must be ≡ -n mod 4
    start_R = 4 - (n % 4)   # positive small congruent
    if start_R == 4:
        start_R = 0
    for R in range(start_R if start_R > 0 else 4, max_R + 1, 4):  # R must stay ≡ -n (mod 4), hence step 4.
        # Actually since step 4 preserves mod 4.
        sol = solve_residual(n, R)
        if sol:
            return (*sol, R)
    return None

def minimal_R_stats(primes: List[int], max_R: int = 100) -> dict:
    stats = {}
    for p in primes:
        res = find_solution_by_residuals(p, max_R)
        if res:
            R = res[3]
            stats[p] = R
        else:
            stats[p] = None
    return stats

if __name__ == "__main__":
    from erdos_straus.solver import generate_hard_primes
    hard = generate_hard_primes(5000)
    print("Hard primes:", hard)
    stats = minimal_R_stats(hard, max_R=100)
    print("Minimal R for each:")
    for p, R in stats.items():
        print(p, R)
    # Count distribution
    from collections import Counter
    print("R distribution:", Counter(stats.values()))
