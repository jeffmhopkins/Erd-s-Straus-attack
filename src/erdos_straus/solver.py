#!/usr/bin/env python3
"""
Erdős–Straus Attack Harness
Framework for searching solutions, testing parametric families, and analyzing hard cases.
"""

from typing import Optional, Tuple, List, Dict
import math
from fractions import Fraction
import itertools

def is_solution(n: int, a: int, b: int, c: int) -> bool:
    """Check if 4/n = 1/a + 1/b + 1/c exactly."""
    if a <= 0 or b <= 0 or c <= 0:
        return False
    return 4 * a * b * c == n * (b * c + a * c + a * b)

def normalize(a: int, b: int, c: int) -> Tuple[int, int, int]:
    return tuple(sorted([a, b, c]))

def solve_for_fixed_a(n: int, a: int) -> Optional[Tuple[int, int]]:
    """
    For fixed a, solve 4/n = 1/a + 1/b + 1/c for positive integers b <= c.
    d = 4a - n > 0.
    1/b + 1/c = d / (n a)
    Let m = n * a
    Then (b + c) / (b c) = d / m  =>  m (b + c) = d b c
    Rearrange to: d b c - m b - m c = 0
    Add m^2 / d : multiply by d: d^2 b c - m d b - m d c = 0
    (d b - m)(d c - m) = m^2
    So let k = d b - m, then k | m^2, k > 0, and b = (k + m)/d must be integer.

    NOTE: this helper is the naive fallback -- it scans b over a bounded
    window rather than factoring m^2, and returns None both when no
    solution exists in the window and when the window exceeds its size
    cap. The real implementations are residual_solver (sympy divisors)
    and bulk_generate (integer-only, at scale).
    """
    if a <= n // 4:
        return None
    d = 4 * a - n
    if d <= 0:
        return None
    m = n * a
    # We need positive divisors k of m*m such that (k + m) % d == 0 and b = (k + m)//d >= a (or 1)
    # Then c = (m^2 / k + m) // d
    target = m * m
    min_b = (m // d) + 1
    max_b = (2 * m) // d   # rough for b <= c
    if max_b - min_b > 100000:  # window too large for the naive scan
        return None
    for b in range(max(min_b, a), max_b + 1):
        denom = b * d - m
        if denom <= 0:
            continue
        if (b * m) % denom == 0:
            c = (b * m) // denom
            if c >= b:
                return (b, c)
    return None

def find_any_solution(n: int, max_a_factor: float = 10.0) -> Optional[Tuple[int, int, int]]:
    """
    Search for a solution with a up to max_a_factor * n.
    Returns (a,b,c) sorted or None.
    """
    if n < 2:
        return None
    # Lower bound a >= ceil((n+3)/4) roughly, but start from ceil(n/4)+1
    start_a = (n // 4) + 1
    max_a = int(max_a_factor * n) + 10
    for a in range(start_a, max_a + 1):
        res = solve_for_fixed_a(n, a)
        if res:
            b, c = res
            return normalize(a, b, c)
    return None

def known_easy_solutions(n: int) -> Optional[Tuple[int, int, int]]:
    """
    Apply classical identities for easy residue classes.
    """
    # n ≡ 0 (mod 4) reduces multiplicatively to 4/k with k = n/4, so no
    # dedicated identity is needed here; callers handle composite n via
    # their smallest prime factor. The classical identity below covers
    # n ≡ 3 (mod 4): with n = 4k+3 and a = k+1, the remainder
    # 4/n - 1/a equals 1/(na), which splits as 1/(na+1) + 1/(na(na+1)).
    if n % 4 == 3:
        k = (n - 3) // 4
        a = k + 1
        m = n * a
        b = m + 1
        c = m * (m + 1)
        if is_solution(n, a, b, c):
            return normalize(a, b, c)
    return None

def hard_residue(n: int) -> bool:
    """True if n mod 840 is in the Mordell hard set."""
    r = n % 840
    return r in {1, 121, 169, 289, 361, 529}

def generate_hard_primes(limit: int = 10000) -> List[int]:
    """Simple sieve for hard primes up to limit."""
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.sqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit+1, i):
                sieve[j] = False
    primes = [p for p in range(2, limit+1) if sieve[p] and hard_residue(p)]
    return primes

# Test basic functionality
if __name__ == "__main__":
    print("Testing solver...")
    tests = [2, 3, 4, 5, 7, 11, 13, 17, 19, 23, 1009]  # 1009 is hard class 1 mod 840
    for n in tests:
        sol = find_any_solution(n, max_a_factor=5.0)
        easy = known_easy_solutions(n)
        print(f"n={n}: any={sol}, easy={easy}, hard={hard_residue(n)}")
    print("Hard primes < 2000:", generate_hard_primes(2000)[:20])
