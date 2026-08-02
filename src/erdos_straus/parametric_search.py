#!/usr/bin/env python3
"""
Search for parametric families in hard classes by fixing residual R and solving the resulting conditions.
"""

from erdos_straus.solver import is_solution
from typing import List, Tuple, Optional

def try_fixed_residual(n: int, R: int) -> Optional[Tuple[int, int, int]]:
    """If n + R divisible by 4, a = (n+R)//4, try to find b,c using the (db - m)(dc - m) = m^2 method with limited search."""
    if (n + R) % 4 != 0 or R <= 0:
        return None
    a = (n + R) // 4
    if a <= 0:
        return None
    m = n * a
    d = R
    # A certificate is k | m**2 with (k + m) % d == 0; writing k = d*t - m,
    # the scan below iterates t = b upward from a and keeps the first t with
    # d*t - m > 0 dividing m**2.
    max_tries = 10000
    for t in range(a, a + max_tries):
        k = d * t - m
        if k <= 0:
            continue
        if m*m % k == 0:
            c_num = m*m // k + m
            if c_num % d == 0:
                c = c_num // d
                if c >= t and is_solution(n, a, t, c):
                    return (a, t, c)
    return None

def search_small_R_for_class(r: int, max_t: int = 20, max_R: int = 100) -> List:
    """For n = 840*t + r, try small R and see for how many t it works."""
    results = []
    for t in range(0, max_t + 1):
        n = 840 * t + r
        if n < 2:
            continue
        found = False
        for R in range(1, max_R + 1, 2):  # odd R
            if (n + R) % 4 == 0:
                sol = try_fixed_residual(n, R)
                if sol:
                    results.append((n, R, sol))
                    found = True
                    break
        if not found:
            results.append((n, None, None))
    return results

if __name__ == "__main__":
    # Test for r=1
    print("Searching for class 1 mod 840, small t...")
    res = search_small_R_for_class(1, max_t=5, max_R=50)
    for item in res:
        print(item)
