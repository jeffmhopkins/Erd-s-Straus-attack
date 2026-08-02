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
| \(< 5 \times 10^7\) | ~93k     | Yes         | 107               | — |
| \(< 1.2 \times 10^8\) | 213 131 | Yes | 107               | Full explicit solutions saved (gzip) |
| \(< 10^9\)     | **1 587 581** | **Yes** | **107**       | Minimal-\(R\) map saved (gzip); current verified bound |

The \(1.2 \times 10^8\) pass was produced by `erdos_straus.bulk_generate`
(integer-only trial-division solver, numpy sieve, 4-way parallel) in **≈9 s**
and independently re-verified with exact integer arithmetic.

The \(10^9\) pass used the **segmented sieve** (bounded memory) and completed
in **≈49 s** on 4 cores. It is stored as a compact minimal-\(R\) map
(`n → R`); explicit triples \((a,b,c)\) reconstruct deterministically from
\((n, R)\), and verification (`es-verify`) re-derives and exactly checks every
triple, so the map is a full certificate set, not a summary.

### Minimal-\(R\) distribution up to \(10^9\) (1 587 581 hard primes)

| \(R\) | count | share | cumul. | | \(R\) | count |
|------:|------:|------:|-------:|-|------:|------:|
| 3  | 779 745 | 49.1 % | 49.1 % | | 43 | 197 |
| 7  | 386 431 | 24.3 % | 73.5 % | | 47 | 318 |
| 11 | 283 978 | 17.9 % | 91.3 % | | 51 | 37 |
| 15 | 60 708  | 3.8 %  | 95.2 % | | 55 | 51 |
| 19 | 43 687  | 2.8 %  | 97.9 % | | 59 | 46 |
| 23 | 22 167  | 1.4 %  | 99.3 % | | 63 | 10 |
| 27 | 3 909   | 0.25 % | 99.56 %| | 67, 75, 83 | 2 each |
| 31 | 4 820   | 0.30 % | 99.87 %| | 71 | 6 |
| 35 | 708     | 0.045 %| 99.91 %| | 79 | 1 |
| 39 | 755     | 0.048 %| 99.96 %| | 107 | 1 (\(p=8\,803\,369\)) |

**Key facts at \(10^9\):**
- Extending the bound by \(20\times\) (from \(5\times 10^7\)) produced
  **no new maximal \(R\)**: the record 107 still comes from the single prime
  \(8\,803\,369 < 10^7\).
- There is a conspicuous **gap**: no prime has minimal \(R \in
  \{87, 91, 95, 99, 103\}\) — the distribution jumps from 83 straight to 107.
- The record prime is genuinely exceptional: no residual below 107 works for
  it **even allowing \(R\) up to 400**; its \(a = (p+107)/4 = 3^2 \cdot 11^2
  \cdot 43 \cdot 47\) is fully smooth, whereas typical high-\(R\) primes have
  an \(a\) with one large prime factor.

## Covering-Set Analysis at \(10^9\) (`analyze.py cover`)

For **every** hard prime \(< 10^9\) we computed the full set of admissible
residuals \(R \equiv 3 \pmod 4\), \(R \le 107\) that yield a solution
(27-bit mask per prime; archived in
`data/analysis/residual_masks_1e9.json.gz`). Findings:

- **Zero uncoverable primes**: the fixed list \(\{3, 7, \dots, 107\}\)
  (all \(R \equiv 3 \bmod 4\)) covers every hard prime below \(10^9\).
- **Individual residuals are far stronger than minimal-\(R\) statistics
  suggest**: \(R=23\) alone solves **72 %** of all hard primes, \(R=47\)
  solves 71 %, \(R=11\) 70 % — minimal-\(R\) counts undersell large
  residuals because small ones win the race.
- **The smallest covering list has 18 residuals**:
  \[\{3, 11, 15, 19, 23, 31, 39, 47, 59, 63, 71, 79, 83, 87, 95, 99, 103, 107\}.\]
  (Greedy set cover after fixing mandatory elements; \(R=7\) is redundant.)
- **Only 4 primes in 1 587 581 have a unique working residual \(\le 107\)** —
  these four *are* the obstruction to a shorter list, one in each of four
  hard classes:

  | \(p\) | only working \(R \le 107\) | \(p \bmod 840\) |
  |------:|---------------------------:|----------------:|
  | 8 803 369    | 107 | 169 |
  | 142 361 209  | 59  | 529 |
  | 287 567 281  | 83  | 1   |
  | 794 037 841  | 63  | 121 |

- Option-count distribution at the thin end: 4 primes with a single option,
  17 with two, 127 with three — the vast majority of primes have many
  working residuals.

**Key observations:**
- Minimal residual \(R\) grows very slowly.
- Distribution is heavily concentrated: \(R=3\) (~40 %), \(R=7\) and \(R=11\) together cover the large majority.
- When \(R=3\) succeeds, the smallest usable divisor \(k\) is typically a small prime factor of \(a\).
- A fixed short list of residuals \(\{3,7,11,\dots,107\}\) covers all hard primes examined so far.

## Files in this Repository
- `src/erdos_straus/solver.py` — core utilities, hard-residue detector, classical identities, prime generation helpers
- `src/erdos_straus/residual_solver.py` — main residual + factoring engine
- `src/erdos_straus/parametric_search.py` — early experiments with fixed-residual parametric searches
- `src/erdos_straus/bulk_generate.py` — fast integer-only solver + monolithic/segmented sieves + parallel driver for large-scale generation
- `src/erdos_straus/analyze.py` — minimal-\(R\) distribution/CDF, covering-set (set cover over full residual masks), and high-\(R\) tail structure analysis
- `src/erdos_straus/verify.py` — independent verification of the stored certificates (full triples and minimal-\(R\) maps)
- `data/hard_primes_1e9_minimalR.json.gz` — minimal-\(R\) map for all 1 587 581 hard primes \(< 10^9\) (gzip; triples reconstruct deterministically)
- `data/hard_primes_1.2e8_solutions.json.gz` — explicit \((R,a,b,c)\) for all 213 131 hard primes \(< 1.2 \times 10^8\) (gzip)
- `data/hard_primes_1e6_solutions.json` — explicit \((R,a,b,c)\) for all hard primes \(< 10^6\)
- `data/hard_primes_2e5_solutions.json` — smaller explicit set
- `data/high_R_primes_5e6.json` — primes that required larger residuals
- `tests/test_solver.py` — unit tests and certificate validation
- `STATUS.md` — this document

All 216 141 bundled certificates pass `es-verify` (exact integer arithmetic).

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
1. ~~Extend explicit residual solutions past \(10^8\).~~ **Done** at
   \(1.2 \times 10^8\) (full triples) and \(10^9\) (minimal-\(R\) map,
   segmented sieve). Maximal minimal \(R\) unchanged at 107 across a
   \(20\times\) extension of the bound.
2. Prove (or disprove) that a short fixed list of residuals always suffices.
   ~~Compute which residuals are unavoidable and the smallest covering list
   up to \(10^9\).~~ **Done** — 18 residuals suffice below \(10^9\), and only
   4 primes force the tail of that list (see Covering-Set Analysis). The
   theoretical question is now sharply posed: show that the density of
   primes with *no* working residual \(\le B\) vanishes (or is empty) for
   some fixed \(B\).
3. Construct a parametric family that covers an entire hard residue class for a fixed small \(R\).
4. Analyze the algebraic conditions (divisor distribution / Jacobi barriers) that force larger \(R\).
   First data point: the record prime's \(a\) is fully smooth
   (\(3^2 11^2 43 \cdot 47\)) — the failure of all \(R < 107\) despite many
   divisors suggests a congruence obstruction rather than a scarcity of
   divisors. The `analyze.py tail` output is the raw material here.
5. Push the minimal-\(R\) map to \(10^{10}\) (runtime scales linearly;
   ~8 min on 4 cores).

---
*Attack ongoing. Framework and data are ready for further extension or theoretical work.*
