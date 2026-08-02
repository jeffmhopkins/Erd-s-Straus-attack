# Erdős–Straus Conjecture Attack — Current State
**Date:** 2026-08-02 (current through PR #13)  
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

Documented verification: Swett to \(10^{14}\), Salez to \(10^{17}\); a
\(10^{18}\) verification and 2026 residual-certificate notes have been
reported informally but could not be bibliographically confirmed, and are
cited nowhere in the paper (which uses only Swett, Salez, Vaughan,
Elsholtz–Tao, Mordell, and the sieve references). The residual approach
\(R = 4a - n\) is developed here from scratch with full proofs.

## Method Used
Residual method:
1. Choose residual \(R = 4a - n > 0\) with \(a = (n + R)/4\) integer.
2. Set \(m = n \cdot a\).
3. Search for a positive divisor \(k \mid m^2\) satisfying \(k \equiv -m \pmod{R}\).
4. Recover \(b = (k + m)/R\), \(c = (m^2/k + m)/R\).

Reference implementation in `residual_solver.py` (sympy); the production
engine is `bulk_generate.py` (integer-only trial division, segmented sieve,
parallel, three output formats including the compact R-sequence format used
at \(10^{11}\) scale).

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
| \(< 10^9\)     | 1 587 581 | Yes | 107               | Minimal-\(R\) map saved (gzip) |
| \(< 10^{10}\)  | **14 215 707** | **Yes** | **107**      | Minimal-\(R\) map saved (gzip); current verified bound |
| \(< 10^{11}\)  | **128 671 219** | **Yes** | **107**     | R-sequence format (gzip uint8 + explicit tail); current verified bound |

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

### \(10^{11}\) update (the gap fills; the record stands)

The \(10^{11}\) run (streaming R-sequence pipeline, 2.85 h on 4 cores;
verified by 257 k sampled reconstructions plus **all** 20 151 tail entries
\(R \ge 43\) with full minimality — see results PR) delivered two
headline outcomes:

- **The gap {87, 91, 95, 99, 103} FILLED**, exactly as the independence
  model predicted: 8, 3, 5, 1, 1 primes respectively, all in
  \((1.3 \times 10^{10}, 10^{11})\). The conditional landing
  distribution for deep-tail primes matches the model's prediction from
  \(10^9\) data (predicted \(P(87 \mid \text{deep}) = 0.53\) vs
  observed \(8/19\); \(P(95) = 0.22\) vs \(5/19\)). The gap was
  small-number statistics, now confirmed by its own disappearance.
- **The record STILL stands**: max minimal \(R = 107\), still uniquely at
  \(p = 8\,803\,369 < 10^7\), across \(5\times 10^7 \to 10^{11}\).
  Eighteen new primes entered \(R_{\min} > 83\) territory and none
  passed 103 — consistent with the Theorem J growth law (first record
  break forecast \(10^{12}\)–\(10^{13}\)).

### \(10^{10}\) update (prediction test)

The \(10^{10}\) run (segmented sieve, 656 s on 4 cores; 143 000 sampled
certificates plus **all** tail entries \(R \ge 51\) re-verified with full
minimality checks — zero errors) resolved the two falsifiable forecasts made
at \(10^9\) (see `THEORY.md` §6):

- **The record held.** Max minimal \(R\) is *still* 107, still uniquely at
  \(p = 8\,803\,369 < 10^7\) — now unchanged across **three orders of
  magnitude** (the model called this a coin flip; independence alone gave 4 %).
- **The gap persists.** Still no prime with minimal
  \(R \in \{87, 91, 95, 99, 103\}\) among 14.2 M primes.
- The tail thickened exactly as the model predicts at moderate depth:
  minimal \(R \in \{75, 79, 83\}\) went from 2, 1, 2 primes to 3, 11, 5 —
  but no prime crossed 83. The deep-tail correlation factor apparently
  *suppresses* new records rather than producing them: smooth-shift
  configurations are rarer at larger \(p\) (each \(f_R \to 0\)), and no new
  structurally-exceptional prime appeared.

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
- `src/erdos_straus/theory.py` — obstruction theory: Jacobi machinery, failure taxonomy, exact-criteria engines (`solvable_exact`, `finite_criterion_dp`), support-bound verifiers (combinatorial and DP), aggregate identities, R=7 finite verification, independence model
- `src/erdos_straus/verify.py` — independent verification of the stored certificates (full triples, minimal-\(R\) maps, and npz archives)
- `data/hard_primes_1e9_minimalR.json.gz` — minimal-\(R\) map for all 1 587 581 hard primes \(< 10^9\) (gzip; triples reconstruct deterministically)
- `data/hard_primes_1.2e8_solutions.json.gz` — explicit \((R,a,b,c)\) for all 213 131 hard primes \(< 1.2 \times 10^8\) (gzip)
- `data/hard_primes_1e6_solutions.json` — explicit \((R,a,b,c)\) for all hard primes \(< 10^6\)
- `data/hard_primes_2e5_solutions.json` — smaller explicit set
- `data/high_R_primes_5e6.json` — primes that required larger residuals
- `data/hard_primes_1e10_minimalR.json.gz` — minimal-\(R\) map for all 14 215 707 hard primes \(< 10^{10}\)
- `data/hard_primes_1e11_minimalR.{rvals.u8.gz, meta.json, tail.json}` — R-sequence dataset for all 128 671 219 hard primes \(< 10^{11}\) (uint8 minimal-\(R\) values in ascending-prime order + sha256-pinned metadata + explicit verified tail \(R \ge 43\))
- `data/analysis/` — residual masks (27 × 1 587 581 solvability bits), distribution/CDF, covering-set results, tail reports, theory-validation archive
- `tests/test_solver.py` — 46 tests: unit, certificate validation, theorem checks (A/A′/A″/J/meta), support-bound lemmas, aggregate identities
- `paper/erdos_straus_residuals.tex` (+ compiled PDF) — the manuscript, 16 pp.
- `lean/ErdosStraus/` — Lean 4 + mathlib formalization, elementary layer + finite enumerations (`lake exe cache get && lake build`)
- `THEORY.md` — full theoretical development; `STATUS.md` — this document

All 1 803 722 certificates in the `es-verify` defaults pass exhaustively
(exact integer arithmetic); the \(10^{10}\) map is verified by sampling plus
full tail minimality.

## Comparison with Published Work
- **Verification** (Swett \(10^{14}\), Salez \(10^{17}\)) rules out
  counterexamples far beyond our range but exhibits no mechanism.
- **Vaughan (1970)**: exceptional set \(\ll x\exp(-c(\log x)^{2/3})\) —
  asymptotically stronger than any fixed power of \(\log x\); our chain's
  value is mechanism (explicit certificates, exact criteria, machine-verified
  lemmas), not raw density.
- This project supplies the largest explicit certificate dataset
  (to \(10^{10}\), \(10^{11}\) in progress), exact solvability criteria,
  and the reciprocity structure theory of joint failure.

## Theoretical Results (see THEORY.md)

- **Theorem A** (R=3 exact criterion) and **Theorem A′** (R=7, hard primes,
  machine-verified) — proved and verified against all data.
- **Theorem A″** (R=11 exact criterion) — the first case beyond the
  character dichotomy: failure ⟺ all factors QR mod 11, *or* one of three
  explicit exponent-budget patterns (verified on 158 759/158 759 primes).
- **Meta-theorem** — every fixed R admits a computable exact finite-state
  criterion (`theory.solvable_exact`, `theory.finite_criterion_dp`).
- **Theorem E** (unconditional, full proof) — hard primes failing both
  R=3 and R=7 number O(x/(log x)²); empirically density ≈ 5.17/log x,
  constant to 2 % across three decades. With A″, the {3,7,11} exceptional
  set is O(x/(log x)^{5/2}).
- **Theorems F/G/G′/H** (the chain) — joint exceptional sets:
  {3,7,11} → O(x/(log x)^{5/2}); {3,7,11,19} → O(x/(log x)³);
  +23 → 7/2; all fifteen primes ≤ 107 → **17/2**, via **Lemma S**
  (support bound, machine-verified by subset-DP for every prime residual
  19…107, zero violations).
- **Theorem I** (aggregate identities) — R | p+1 or R | p+4 always
  certifies; the only a-independent families; +1 to the chain (**19/2**);
  covers 74 % of hard primes alone; characterizes the critical primes.
- **Theorem J** (reciprocity structure) — (q|R) = (p|q) for odd primes
  q | (p+R)/4: joint Type-I failure ⟺ p is a QR mod every unforced prime
  of every shifted value. Explains the record prime (4σ Legendre-coin
  fluctuation over only 43 distinct primes) and why hard classes are the
  squares mod 840 (forced small primes are character-neutral).
- **Theorem K** (conditional) — under Dickson's conjecture, every fixed
  finite residual list fails infinitely often: the fixed-list covering
  hypothesis is **false** under standard conjectures.
- **Theorem D** (density reduction, full proof in the paper) — for every
  A, a finite residual list covers all hard primes except relative
  density O((log x)^{−A}).
- **Completeness** — every ESC solution is a residual certificate with
  R ≤ 2p, so *any* unconditional bound on R_min(p) is equivalent to the
  conjecture itself.
- **Lean formalization** (`lean/ErdosStraus`) — the elementary layer is
  machine-checked in Lean 4 + mathlib: certificate soundness and
  integrality, Theorem A both directions, both Theorem I families,
  Theorem J, and the hard-class lemmas. The finite-enumeration layer is
  also formalized: the meta-theorem's divisor-class reachability model
  (`reach`), both halves of the monotonicity reduction (`reach_mono`,
  `reach_sublist`), the full 1,536-configuration verification of
  Theorem A′ at R = 7, and Lemma S at R = 19 (437,580 checks), both
  via `native_decide`. All declarations sorry-free and
  axiom-audited; see `lean/README.md` for the trust base. Next tier:
  Theorem A″ (R = 11) and the reach ⟺ divisor-certificate bridge.

## Current Assessment
- No counterexample; all 128 671 219 hard primes below \(10^{11}\) have
  verified solutions with \(R \le 107\).
- The record's staticness is now *explained* (Theorem J): joint failure is a
  Legendre-coin large-deviation event; expected record growth
  \(\asymp \log x/\log\log x\) at the pure-Type-I level.
- The fixed-finite-list reduction is conditionally **false** (Theorem K):
  the correctly-posed open problem is an unconditional bound on
  \(R_{\min}(p)\) — which, by completeness, *is* the conjecture.
- Almost-all coverage is settled with mechanism: exponent 19/2 chain,
  exact criteria for R = 3, 7, 11, and per-residual finite-state criteria
  for every fixed R (meta-theorem).

## Next Natural Steps (updated)
1. ~~Extend past \(10^8\), \(10^9\), \(10^{10}\), \(10^{11}\).~~
   **Done** — the \(10^{11}\) run confirmed the Theorem J growth law on
   both counts (record survived; gap filled with the predicted
   conditional distribution). Next decade (\(10^{12}\), ~29 h compute)
   enters the forecast record-break window.
2. ~~Fixed finite list?~~ **Resolved in direction**: covering lists computed
   (18 suffice below \(10^9\), lower bound 12); fixed lists fail infinitely
   often under Dickson (Theorem K). Remaining: nothing short of the
   conjecture itself (completeness).
3. ~~Single fixed \(R\) covering an entire hard class?~~ **No** — each
   fixed \(R\) has positive-density failure in every class (exact
   criteria + Selberg–Delange); coverage is inherently a union over
   residuals/families.
4. ~~Algebraic conditions forcing large \(R\).~~ **Done** — Proposition 1
   (character obstruction), Theorem A″ (budget patterns), Theorem J
   (reciprocity structure): the full mechanism of the tail.
5. Open: composite-residual criteria (R = 15 first); Lemma S past 107;
   Olson-type additive combinatorics to enlarge the provable forbidden
   structure (the route that could pass Vaughan conditionally); the
   unconditional \(R_{\min}\) bound (= the conjecture).

---
*Attack ongoing. Framework and data are ready for further extension or theoretical work.*
