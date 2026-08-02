# Erdős–Straus Conjecture Attack — Current State
**Date:** 2026-08-01 / 2026-08-02  
**Focus:** Hard-class primes (Mordell exceptional residues mod 840)

## The Problem
The Erdős–Straus conjecture asserts that for every integer \(n \ge 2\) there exist positive integers \(a,b,c\) such that
\[
\frac{4}{n} = \frac{1}{a} + \frac{1}{b} + \frac{1}{c}.
\]
It is known for all \(n\) outside six residue classes modulo 840:
\[
\{1, 121, 169, 289, 361, 529\}.
\]
The remaining open cases are concentrated on primes in these classes (“hard primes”).

Published verification (Salez → Mihnea–Dumitru 2025) has ruled out counterexamples for all \(n \le 10^{18}\) via modular sieves. The residual / certificate approach (\(R = 4a - n\)) appears in 2026 technical notes and is the framework used here.

## Method Used
Residual method:
1. Choose residual \(R = 4a - n > 0\) with \(a = (n + R)/4\) integer.
2. Set \(m = n \cdot a\).
3. Search for a positive divisor \(k \mid m^2\) satisfying \(k \equiv -m \pmod{R}\).
4. Recover \(b = (k + m)/R\), \(c = (m^2/k + m)/R\).

This is implemented in `residual_solver.py` (factoring via sympy) and supported by utilities in `solver.py`.

## Computational Results (Hard Primes Only)

| Bound          | # Hard Primes | All Solved? | Max Minimal \(R\) | Notes |
|----------------|---------------|-------------|-------------------|-------|
| \(< 10^6\)     | 2 370         | Yes         | 59                | Full explicit solutions saved |
| \(< 2 \times 10^6\) | 4 519     | Yes         | 59                | — |
| \(< 5 \times 10^6\) | 10 711    | Yes         | 59                | — |
| \(< 10^7\)     | 20 513        | Yes         | 107               | First appearance of \(R=107\) at \(p=8803369\) |
| \(< 2 \times 10^7\) | ~39k     | Yes         | 107               | — |
| \(< 3 \times 10^7\) | ~57k     | Yes         | 107               | — |
| \(< 5 \times 10^7\) | ~93k     | Yes         | 107               | Current verified bound |

**Key observations:**
- Minimal residual \(R\) grows very slowly.
- Distribution is heavily concentrated: \(R=3\) (~40 %), \(R=7\) and \(R=11\) together cover the large majority.
- When \(R=3\) succeeds, the smallest usable divisor \(k\) is typically a small prime factor of \(a\).
- A fixed short list of residuals \(\{3,7,11,\dots,107\}\) covers all hard primes examined so far.

## Files in this Repository
- `src/erdos_straus/solver.py` — core utilities, hard-residue detector, classical identities, prime generation helpers
- `src/erdos_straus/residual_solver.py` — main residual + factoring engine
- `src/erdos_straus/parametric_search.py` — early experiments with fixed-residual parametric searches
- `src/erdos_straus/verify.py` — independent verification of the stored certificates
- `data/hard_primes_1e6_solutions.json` — explicit \((R,a,b,c)\) for all hard primes \(< 10^6\)
- `data/hard_primes_2e5_solutions.json` — smaller explicit set
- `data/high_R_primes_5e6.json` — primes that required larger residuals
- `tests/test_solver.py` — unit tests and certificate validation
- `STATUS.md` — this document

All 3010 bundled certificates pass `es-verify` (exact integer arithmetic).

## Comparison with Published Work
- **Full verification to \(10^{18}\)** (Mihnea–Dumitru 2025) is far stronger for ruling out counterexamples; it uses modular sieves rather than exhibiting solutions.
- Residual-certificate theory (2026 notes) already formalizes the \(R=4a-n\) framework and proves that \(R=3\) or \(7\) covers many non-hard cases.
- This attack supplies large-scale *explicit* residual solutions and systematic statistics on the growth of minimal \(R\) for hard primes (up to \(5 \times 10^7\)).

## Current Assessment
- No counterexample found; all hard primes up to 50 million possess explicit solutions with \(R \le 107\).
- The slow growth of minimal residual is the most interesting structural signal.
- A proof that every hard prime admits a solution with \(R\) belonging to a fixed finite set would reduce the conjecture to a finite number of residual shells.
- Parametric constructions with constant \(k\) give positive-density coverage inside each hard class; full arithmetic-progression coverings require more sophisticated (higher-degree or residual-dependent) factors.

## Next Natural Steps
1. Extend explicit residual solutions past \(10^8\).
2. Prove (or disprove) that a short fixed list of residuals always suffices.
3. Construct a parametric family that covers an entire hard residue class for a fixed small \(R\).
4. Analyze the algebraic conditions (divisor distribution / Jacobi barriers) that force larger \(R\).

---
*Attack ongoing. Framework and data are ready for further extension or theoretical work.*
