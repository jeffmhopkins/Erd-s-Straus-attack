# Erdős–Straus Conjecture Attack — Current State
**Date:** 2026-08-04 (current through PR #58 — the $10^{12}$ census)  
**Focus:** Hard-class primes (Mordell exceptional residues mod 840)

## The Problem
The Erdős–Straus conjecture asserts that for every integer $n \ge 2$ there exist positive integers $a,b,c$ such that
$$
\frac{4}{n} = \frac{1}{a} + \frac{1}{b} + \frac{1}{c}.
$$
It is known for all $n$ outside six residue classes modulo 840:
$$
\{1, 121, 169, 289, 361, 529\}.
$$
The remaining open cases are concentrated on primes in these classes (“hard primes”).

Documented verification: Swett to $10^{14}$, Salez to $10^{17}$, and
Mihnea–Bogdan to $10^{18}$ (arXiv:2509.00128) — all three now
web-verified and cited in the paper, alongside Erdős 1950, Vaughan,
Elsholtz–Tao, Mordell, and the sieve references. The residual approach
$R = 4a - n$ is developed here from scratch with full proofs.

## Method Used
Residual method:
1. Choose residual $R = 4a - n > 0$ with $a = (n + R)/4$ integer.
2. Set $m = n \cdot a$.
3. Search for a positive divisor $k \mid m^2$ satisfying $k \equiv -m \pmod{R}$.
4. Recover $b = (k + m)/R$, $c = (m^2/k + m)/R$.

Reference implementation in `residual_solver.py` (sympy); the production
engine is `bulk_generate.py` (integer-only trial division, segmented sieve,
parallel, three output formats including the compact R-sequence format used
at $10^{11}$ and $10^{12}$ scale).

## Computational Results (Hard Primes Only)

| Bound          | # Hard Primes | All Solved? | Max Minimal $R$ | Notes |
|----------------|---------------|-------------|-------------------|-------|
| $< 10^6$     | 2 370         | Yes         | 59                | Full explicit solutions saved |
| $< 2 \times 10^6$ | 4 519     | Yes         | 59                | — |
| $< 5 \times 10^6$ | 10 711    | Yes         | 59                | — |
| $< 10^7$     | 20 513        | Yes         | 107               | First appearance of $R=107$ at $p=8\,803\,369$ |
| $< 2 \times 10^7$ | ~39k     | Yes         | 107               | — |
| $< 3 \times 10^7$ | ~57k     | Yes         | 107               | — |
| $< 5 \times 10^7$ | ~93k     | Yes         | 107               | — |
| $< 1.2 \times 10^8$ | 213 131 | Yes | 107               | Full explicit solutions saved (gzip) |
| $< 10^9$     | 1 587 581 | Yes | 107               | Minimal-$R$ map saved (gzip) |
| $< 10^{10}$  | 14 215 707 | Yes | 107      | Minimal-$R$ map saved (gzip) |
| $< 10^{11}$  | 128 671 219 | Yes | 107     | R-sequence format (gzip uint8 + explicit tail) |
| $< 10^{12}$  | **1 175 215 396** | **Yes** | **111** | **Record broken** — first row since $10^7$ where the max is not 107; attained by 3 primes, least $p = 119\,945\,383\,009$. R-sequence format; current verified bound |

*(Every row is "all solved" with a certificate at the stated maximal
minimal residual; `num_unsolved = 0` at $10^{12}$ as at every earlier
bound.)*

The $1.2 \times 10^8$ pass was produced by `erdos_straus.bulk_generate`
(integer-only trial-division solver, numpy sieve, 4-way parallel) in **≈9 s**
and independently re-verified with exact integer arithmetic.

The $10^9$ pass used the **segmented sieve** (bounded memory) and completed
in **≈49 s** on 4 cores. It is stored as a compact minimal-$R$ map
(`n → R`); explicit triples $(a,b,c)$ reconstruct deterministically from
$(n, R)$, and verification (`es-verify`) re-derives and exactly checks every
triple, so the map is a full certificate set, not a summary.

*(The subsections below are organized around the exhaustively verified
$10^9$ baseline, with the $10^{12}$, $10^{11}$ and $10^{10}$ updates
interleaved newest-first.)*

### Minimal-$R$ distribution up to $10^9$ (1 587 581 hard primes)

| $R$ | count | share | cumul. | | $R$ | count |
|------:|------:|------:|-------:|-|------:|------:|
| 3  | 779 745 | 49.1 % | 49.1 % | | 43 | 197 |
| 7  | 386 431 | 24.3 % | 73.5 % | | 47 | 318 |
| 11 | 283 978 | 17.9 % | 91.3 % | | 51 | 37 |
| 15 | 60 708  | 3.8 %  | 95.2 % | | 55 | 51 |
| 19 | 43 687  | 2.8 %  | 97.9 % | | 59 | 46 |
| 23 | 22 167  | 1.4 %  | 99.3 % | | 63 | 10 |
| 27 | 3 909   | 0.25 % | 99.56 % | | 67, 75, 83 | 2 each |
| 31 | 4 820   | 0.30 % | 99.87 % | | 71 | 6 |
| 35 | 708     | 0.045 % | 99.91 % | | 79 | 1 |
| 39 | 755     | 0.048 % | 99.96 % | | 107 | 1 ($p=8\,803\,369$) |

### Burgess/reciprocity census (newest)

Full-population scan below $10^9$ (THEORY.md §2.10,
`data/analysis/burgess_scan_1e9.json`): taking each hard prime's least
Legendre non-residue $q$ ($q \ge 11$; observed $\le 83$) and the
selected residual $R \equiv -p \pmod{4q}$, **94.78 %** of all
1 587 581 hard primes succeed at the single selected residual; the
$q$-ladder ($R + 4qk \le 400$) resolves all but 1 295, and a second
non-residue $q$ resolves **every** remaining prime — 100 % coverage
with $R \le 400$. Failures are budget-type in 82 401 of 82 808 cases
(407 per-prime character cases at composite $R$). Composite-Jacobi
reciprocity $(q|R) = (p|q)$ verified at every selected residual, zero
violations. Purity (non-residue factor $\Rightarrow$ success) holds
exactly at the proved $R = 3, 7, 15$ and fails everywhere else.
**Scaled to $10^{11}$** (`burgess_scan_1e10_1e11.json`): first-shot
rate is flat at 95.0–95.8 % across four half-decade window samples
(10 000 primes each, ladder coverage 100 %), and on the complete
$10^{11}$ deep tail (all 20 151 primes with $R_{\min} \ge 43$) the
ladder resolves all but two primes at cap 400 — both resolve by
$R = 435$. No drift in the per-rung budget-failure rate with $p$. **Failure
anatomy** (`burgess_failures_1e9.json`): 97.5 % of failures are true
budget misses (29 % miss only the target class); no failure has more
than 5 non-identity factor classes, with $P(\text{fail} \mid s)$
falling $\sim 7\times$ per class
($27\% \to 8\% \to 1.2\% \to 0.08\% \to 0$); non-residue mass sits
at its consistency-parity minimum in 97.9 % of failures. **Drafted** (THEORY.md §2.10):
Theorem L₀ — the rigorous fixed-length ladder chain (dimension 1/2
per rung via Theorem S, p-adapted residuals); Hypothesis B — the
falsifiable per-rung counting inequality the census measures
(per-rung survival factor 0.05–0.14 — 86–95 % of surviving failures
resolve at each rung — no drift); **Theorem B₁ proved**: B's first rung — for every fixed $q$ the
selected-rung failing fraction is
$\ll_q (\log x)^{-1/\varphi(R_0)} \to 0$ (Prop 2.2's universal
class + Fundamental Lemma), uniformly
for $q \ll \log\log x$; mechanism exact in data (0 violations /
11 816 failures) and 25.5 % of primes get the closed-form
$k = q p^2$. **Theorem B₂ proved** (two-sided proxy ladder: beta-sieve lower +
Fundamental-Lemma upper give $\#\tilde E_J \asymp x/(\log x)^{1+\kappa}$,
so the avoidance ladder decays exactly as B prescribes), and
**B reduces to Hypothesis P** (failures ≥ $c_P$ · avoiders; measured
$c_P$ = 12.0 % at rung 0, 15.9 % at rung 1, archive
`burgess_proxy_1e9.json`; **stable at scale**: $c_P$ = 9.7–11.6 % across four half-decade bins to $10^{11}$, `burgess_proxy_scaled.json`): under P, B holds at every fixed rung — the
program is L₀ ✓, B₁ ✓, B₂ ✓, B ⟸ P, L₁ ⟸ B, with P the single
unproved ingredient, bracketed on both sides only on a sparse family
of classes and one-sidedly (upper bound) elsewhere. The lower-bound
side comes from the **norm-form bridge** (paper eq. (5.1)): for
$r \equiv 3 \pmod 4$, "every prime factor of $a$ is a QR mod $r$" is
"$a$ is *primitively* represented by a binary quadratic form of
discriminant $-r$", so character failure families are norm-form families
and Iwaniec's *prime-indexed* half-dimensional sieve (Acta Arith. 21
(1972) 203–234) is the counting tool — parity does not bite at
$\kappa = 1/2$, where $\beta(1/2) = 1$. It gives **Theorem 5.7 (the
first link is sharp)**: the hard primes $p \le x$ failing $R$ number
$\asymp x/(\log x)^{3/2}$ for $R = 3, 7, 15$ (one-sided bounds
separately at $R = 11$), and by Theorem S the exponent $3/2$ is the
*ceiling* of the method — every failure-sufficient family has sieve
dimension $\ge 1/2$, so there is no weaker-exponent fallback. Along
the ladder, **Theorem 5.8** (the corrected former "Theorem P₁" —
the printed statement was **false**, its admissibility test having
ignored the small primes the class forces to divide $a$; see the
correction note in THEORY §2.10) gives
$\#E_0 \gg x/(\log x)^{3/2}$ only on classes passing the completed
conditions (A1)–(A3), which is **0.023 %** of first rungs (9 of
39 391 hard $p \le 2\times10^7$), not the 6.6 % previously claimed —
that figure counted only (A1), on which the family can be empty; and
whenever $R_0$ is prime (the typical case) no such $r_1$ exists at
all. On that sparse family, at rung 0 only, the gap to P is
$(\log x)^{1/2 - 1/\varphi(R_0)}$; elsewhere P is not bracketed from
below at all. Theorem L₁ — under
B, all but $O(x e^{-\delta J(x)})$ hard primes have
$R_{\min}(p) \le (\log x)^{2+o(1)} J(x)$; calibrations from
$J = (\log\log x)^2$ (past the entire chain) to
$J = (\log x)^{\theta}$, $\theta > 2/3$ (past Vaughan).

**Theorem U (proved, unconditional — THEORY §2.11, paper Thm 4.5):**
the uniform chain. All but $O(x\exp(-c(\log\log x)^2))$ hard primes
$p \le x$ have $R_{\min}(p) \le \varepsilon\log\log x$ — no
Hypothesis B, no P, no $q(p)$; Brun's sieve over a residual list of
length $\varepsilon\log\log x$ with the general-$\omega$ Kneser tier
of Theorem S(iii) and tracked uniform constants (ineffective via
Siegel–Walfisz). This delivers L₁'s mild calibration unconditionally
with a stronger $R_{\min}$ bound; B's real content is now the
$\theta$-calibrations past the $\exp(-c(\log\log x)^2)$ ceiling
(paper Rem 4.6: the branch factor is the only binding wall; the
class conditioning resums and Siegel–Walfisz reaches any fixed power
of $\log x$). Two obstruction
computations (paper Rem 5.13) close the August 2026 research routes:
budget failure is provably not a character event (explicit witness
pair at $R = 11$), and weighted/almost-prime detection is equivalent
to Hypothesis P — the parity gap is intrinsic.

**Branch classification (THEORY §2.12, paper §4.2):** the structural
question behind Theorem U's ceiling is now half-solved. Proved:
kernel branches reduce losslessly to aperiodic maximal supports
(Thm 4.8); the count form is false (≥ $2^{c\sqrt d}$ maximal
supports, Thm 4.7); size spectrum $\Theta(\log d)$ to $d/2-1$;
near-critical Kneser is vacuous here (slack rigidity). Open:
**Conjecture A** (Conj 4.9) — every aperiodic maximal failing
support fits a window container (coset-progression) of density
≤ 1/2; verified exhaustively at all moduli $d \le 30$ (all targets)
and at $R = 19, 23, 31, 43, 47, 59$ + composites $15, 35, 39$
(495,782 maximal supports at $R = 59$; zero unstructured). Under A:
branch count drops $2^{\varphi(R)} \to O(R^2)$ and the uniform
chain reaches the **polylog tier** (Thm 4.11):
$R_{\min} \le (\log x)^{c_0}$ outside
$x\exp(-(\log x)^{c_0})$, $c_0 \approx 1/9$, family ceiling $1/2$.
Enumeration entry point `erdos_straus.branch_enum`, archive
`data/analysis/branch_maximal_supports.json`.

**Conjecture A round (THEORY §2.13):** no counterexample anywhere —
exhaustive at every $d \le 60$ and at $d = 72$, the smallest
non-Hajós order (14.99M maximal supports); sampled to 240. The
feared punctured-chain mechanism is **provably empty** (β-vacuity,
paper Prop 4.12: a β-step forces the deleted element into the
stabilizer), and Conjecture A restricted to Hajós orders already
yields the polylog tier at the same exponent up to $o(1)$ (Chen-type
$P_3$ count of good residuals). Remaining: non-critical-step control
at the $|F| = 2$ floor + the prime-power two-scale coupling.
Archive: `data/analysis/conjA_verification.json`.

### $10^{12}$ update (THE RECORD BREAKS) — newest

The $10^{12}$ run (single scripted pass, `scripts/run_1e12.sh`: 10.5 h
wall on 32 cores of an AMD Ryzen AI Max+ 395, of which 53 min sieving;
`sieve_secs` 3170.2, `elapsed_secs` 37707.1) covered all
**1 175 215 396** hard primes below $10^{12}$. Zero unsolved; every one
has a certificate with $R \le 111$. Verification: 2 350 431
systematically sampled entries reconstructed and exactly re-checked,
plus **all** 118 210 tail entries ($R \ge 43$) with full minimality
(no smaller admissible $R$ succeeds) — `bad = 0`, `not_minimal = 0`,
log ends `VERIFICATION OK`.

- **The record broke.** Max minimal $R$ is now **111**, first attained at
  $$p = 119\,945\,383\,009 \equiv 529 \pmod{840},$$
  for which every admissible $R \le 107$ fails and $R = 111$ certifies
  with $a = (p+111)/4 = 29\,986\,345\,780$ (checked independently by a
  direct solver run and by exact evaluation of the identity). Three
  primes attain 111: 119 945 383 009, 654 730 707 409, 761 403 297 769.
- **107 is no longer unique.** The old record, held by the single prime
  $8\,803\,369 < 10^7$ from $10^7$ through $10^{11}$ — five successive orders of magnitude —
  picked up three further primes in this decade (170 230 867 921,
  269 646 744 481, 565 158 121 441) and now stands at four.
- **Deep tail.** Primes with $R_{\min} \ge 87$ went from 19 at $10^{11}$
  to **73**: counts 40, 5, 12, 4, 5, 4, 3 over
  $R = 87, 91, 95, 99, 103, 107, 111$.
- **Head.** $R = 3$ covers 56.0 %, $\{3,7,11\}$ covers 94.6 %,
  $R \le 23$ covers 99.73 % — the same slow drift upward in the $R=3$
  share seen at every previous decade (49.1 % at $10^9$, 54.4 % at
  $10^{11}$). Full distribution in
  `data/hard_primes_1e12_minimalR.meta.json`.

**A prediction confirmed, stated carefully.** The calibrated
independence model of `THEORY.md` §6 was fitted on the complete $10^9$
solvability masks. It made two falsifiable calls: (a) the then-empty
band $\{87,\dots,103\}$ was small-number statistics and would fill —
it filled at $10^{11}$; and (b) the mass at or beyond $R = 107$ is 6 %
per deep-tail prime, which with the deep-tail growth rate places the
*first record-breaking prime* in the decade $10^{11}$–$10^{12}$ — it
broke there, at $R = 111$. So a heuristic fitted at $10^9$ named in
advance both the band it would fill and the decade in which a
record would move for the first time in five orders of magnitude. Two caveats keep this honest: the
model is a heuristic, not a theorem; and the band-fill comparison had
little discriminating power ($\chi^2 \approx 1.3$ on 19 points with
several expected cells below 5). The record-break call is the sharper
of the two, and it is the one that was confirmed at $10^{12}$.

**Dataset note.** `data/hard_primes_1e12_minimalR.meta.json` and
`.tail.json` are in the repository. The third file of the set, the
304 MB value array `hard_primes_1e12_minimalR.rvals.u8.gz`, exceeds
GitHub's 100 MB per-file limit and is **gitignored** — it is regenerated
deterministically by `scripts/run_1e12.sh` and checked against the
SHA-256 pinned in `meta.json` (`sha256_rvals` `7736d10b…`,
`sha256_primes` `ae1e4e76…`).

### $10^{11}$ update (the gap fills; the record stands)

The $10^{11}$ run (streaming R-sequence pipeline, 2.85 h on 4 cores;
verified by 257 k sampled reconstructions plus **all** 20 151 tail entries
$R \ge 43$ with full minimality — see results PR) delivered two
headline outcomes:

- **The gap {87, 91, 95, 99, 103} FILLED**, exactly as the independence
  model predicted: 8, 3, 5, 1, 1 primes respectively, all in
  $(1.3 \times 10^{10}, 10^{11})$. The conditional landing
  distribution for deep-tail primes matches the model's prediction from
  $10^9$ data (predicted $P(87 \mid \text{deep}) = 0.53$ vs
  observed $8/19$; $P(95) = 0.22$ vs $5/19$ — here 19 counts all
  primes with $R_{\min} > 83$, i.e. the 18 newly appearing deep-tail
  primes plus the pre-existing record prime). The gap was
  small-number statistics, now confirmed by its own disappearance.
- **The record STILL stands** (at this bound): max minimal $R = 107$,
  still uniquely at $p = 8\,803\,369 < 10^7$, across
  $5\times 10^7 \to 10^{11}$.
  Eighteen new primes entered $R_{\min} > 83$ territory and none
  passed 103. It fell in the very next stretch: the first prime with
  $R_{\min} = 111$ is $1.199\times 10^{11}$, barely above this bound —
  see the $10^{12}$ subsection above. (The independence model's window
  for the break was the decade $10^{11}$–$10^{12}$; the coarser
  Theorem J growth-law reading recorded here at the time,
  $10^{12}$–$10^{13}$, was late by a decade.)

### $10^{10}$ update (prediction test)

The $10^{10}$ run (segmented sieve, 656 s on 4 cores; 143 000 sampled
certificates plus **all** tail entries $R \ge 51$ re-verified with full
minimality checks — zero errors) resolved the two falsifiable forecasts made
at $10^9$ (see `THEORY.md` §6):

- **The record held.** Max minimal $R$ is *still* 107, still uniquely at
  $p = 8\,803\,369 < 10^7$ — now unchanged across **three orders of
  magnitude** (the model called this a coin flip; independence alone gave 4 %).
- **The gap persists.** Still no prime with minimal
  $R \in \{87, 91, 95, 99, 103\}$ among 14.2 M primes.
- The tail thickened exactly as the model predicts at moderate depth:
  minimal $R \in \{75, 79, 83\}$ went from 2, 1, 2 primes to 3, 11, 5 —
  but no prime crossed 83. At the time this suggested the deep-tail
  correlation factor *suppresses* new records rather than producing
  them (smooth-shift configurations being rarer at larger $p$).
  **The $10^{12}$ run overturned that reading**: the deep tail grew
  19 → 73 and the $R \ge 107$ share came in above the model's, so the
  $10^{10}$ non-record was simply one draw of a low-probability event.

### Key facts at $10^9$
- Extending the bound by $20\times$ (from $5\times 10^7$) produced
  **no new maximal $R$**: the record 107 still came from the single prime
  $8\,803\,369 < 10^7$ (it stayed that way until $10^{12}$, where
  $R = 111$ appears and 107 acquires three more primes — see above).
- At $10^9$ there was a conspicuous **gap** (filled at $10^{11}$, see
  above): no prime below $10^9$ has minimal
  $R \in \{87, 91, 95, 99, 103\}$ — the distribution jumps from 83 straight to 107.
- The record prime is genuinely exceptional: no residual below 107 works for
  it **even allowing $R$ up to 400**; its
  $a = (p+107)/4 = 3^2 \cdot 11^2 \cdot 43 \cdot 47$ is fully smooth,
  whereas typical high-$R$ primes have an $a$ with one large prime factor.

## Covering-Set Analysis at $10^9$ (`analyze.py cover`)

For **every** hard prime $< 10^9$ we computed the full set of admissible
residuals $R \equiv 3 \pmod 4$, $R \le 107$ that yield a solution
(27-bit mask per prime; archived in
`data/analysis/residual_masks_1e9.json.gz`). Findings:

- **Zero uncoverable primes**: the fixed list $\{3, 7, \dots, 107\}$
  (all $R \equiv 3 \bmod 4$) covers every hard prime below $10^9$.
- **Individual residuals are far stronger than minimal-$R$ statistics
  suggest**: $R=23$ alone solves **72 %** of all hard primes, $R=47$
  solves 71 %, $R=11$ 70 % — minimal-$R$ counts undersell large
  residuals because small ones win the race.
- **The smallest covering list has 18 residuals**:
  $$\{3, 11, 15, 19, 23, 31, 39, 47, 59, 63, 71, 79, 83, 87, 95, 99, 103, 107\}.$$
  (Greedy set cover after fixing mandatory elements; $R=7$ is redundant.)
- **Only 4 primes in 1 587 581 have a unique working residual $\le 107$** —
  these four *are* the obstruction to a shorter list, one in each of four
  hard classes:

  | $p$ | only working $R \le 107$ | $p \bmod 840$ |
  |------:|---------------------------:|----------------:|
  | 8 803 369    | 107 | 169 |
  | 142 361 209  | 59  | 529 |
  | 287 567 281  | 83  | 1   |
  | 794 037 841  | 63  | 121 |

- Option-count distribution at the thin end: 4 primes with a single option,
  17 with two, 127 with three — the vast majority of primes have many
  working residuals.

### Key observations ($10^9$)
- Minimal residual $R$ grows very slowly.
- Distribution is heavily concentrated: $R=3$ alone covers 49.1 % at $10^9$ (54.4 % at $10^{11}$, 56.0 % at $10^{12}$); $R = 3, 7, 11$ together cover 91.3 % (94.6 % at $10^{12}$).
- When $R=3$ succeeds, the smallest usable divisor $k$ is typically a small prime factor of $a$.
- A fixed short list of residuals covers all hard primes examined so far —
  but the list is no longer $\{3,7,11,\dots,107\}$: three primes below
  $10^{12}$ need $R = 111$, so the shortest prefix list that works to
  $10^{12}$ is $\{3,7,11,\dots,111\}$.

## Files in this Repository
- `src/erdos_straus/solver.py` — core utilities, hard-residue detector, classical identities, prime generation helpers
- `src/erdos_straus/residual_solver.py` — main residual + factoring engine
- `src/erdos_straus/parametric_search.py` — early experiments with fixed-residual parametric searches
- `src/erdos_straus/bulk_generate.py` — fast integer-only solver + monolithic/segmented sieves + parallel driver for large-scale generation
- `src/erdos_straus/analyze.py` — minimal-$R$ distribution/CDF, covering-set (set cover over full residual masks), and high-$R$ tail structure analysis
- `src/erdos_straus/theory.py` — obstruction theory: Jacobi machinery, failure taxonomy, exact-criteria engines (`solvable_exact`, `finite_criterion_dp`, composite-R `solvable_exact_general`), R=7/R=15 finite verifications, support-bound verifiers (combinatorial, DP, strong/Kneser form, general abelian), aggregate identities, independence model
- `src/erdos_straus/burgess_scan.py` — Burgess/reciprocity-route census: least Legendre non-residue, selected residuals, Jacobi purity scan, retry ladders (results: `data/analysis/burgess_scan_1e9.json`; THEORY.md §2.10)
- `src/erdos_straus/verify.py` — independent verification of the stored certificates (full triples, minimal-$R$ maps, and npz archives)
- `data/hard_primes_1e9_minimalR.json.gz` — minimal-$R$ map for all 1 587 581 hard primes $< 10^9$ (gzip; triples reconstruct deterministically)
- `data/hard_primes_1.2e8_solutions.json.gz` — explicit $(R,a,b,c)$ for all 213 131 hard primes $< 1.2 \times 10^8$ (gzip)
- `data/hard_primes_1e6_solutions.json` — explicit $(R,a,b,c)$ for all hard primes $< 10^6$
- `data/hard_primes_2e5_solutions.json` — smaller explicit set
- `data/high_R_primes_5e6.json` — primes that required larger residuals
- `data/hard_primes_1e10_minimalR.json.gz` — minimal-$R$ map for all 14 215 707 hard primes $< 10^{10}$
- `data/hard_primes_1e11_minimalR.{rvals.u8.gz, meta.json, tail.json}` — R-sequence dataset for all 128 671 219 hard primes $< 10^{11}$ (uint8 minimal-$R$ values in ascending-prime order + sha256-pinned metadata + explicit verified tail $R \ge 43$)
- `data/hard_primes_1e12_minimalR.{meta.json, tail.json}` — the same format for all 1 175 215 396 hard primes $< 10^{12}$: full $R$-distribution, sha256 pins and run timings, plus the 118 210 explicit verified tail certificates $R \ge 43$ (including the three with $R = 111$). The matching 304 MB value array `hard_primes_1e12_minimalR.rvals.u8.gz` is **not in git** — it exceeds GitHub's 100 MB file limit, so it is gitignored and regenerated deterministically by `scripts/run_1e12.sh`, verified against `sha256_rvals` in the meta file
- `scripts/run_1e12.sh` (+ `scripts/RUN_1E12.md`) — the one-shot $10^{12}$ generation + verification + packaging run kit
- `data/analysis/` — residual masks (27 × 1 587 581 solvability bits), distribution/CDF, covering-set results, tail reports, theory-validation archive
- `tests/test_solver.py` — 63 tests: unit, certificate validation, theorem checks (A/A′/A″/A‴/J/meta incl. composite R), support-bound lemmas (DP + strong Kneser form, cyclic and general abelian), aggregate identities
- `paper/erdos_straus_residuals.tex` (+ compiled PDF) — the manuscript, 40 pp., restructured as a computational paper: "Minimal residual certificates for the Erdős–Straus conjecture: a verified census to $10^{12}$". §1 introduction and provenance, §2 obstruction framework, §3 exact criteria, **§4 the census** (verification protocol, data, record, calibrated model), §5 structural context (sieve chain → Theorem U → branch classification → the conditional ladder, compressed), §6 open problems, Appendix A verification details
- `lean/ErdosStraus/` — Lean 4 + mathlib formalization, elementary layer + finite enumerations (`lake exe cache get && lake build`)
- `THEORY.md` — full theoretical development; `STATUS.md` — this document

All 1 803 722 certificates in the `es-verify` defaults pass exhaustively
(exact integer arithmetic); the $10^{10}$ map is verified by sampling plus
full tail minimality.

## Comparison with Published Work
- **Verification** (Swett $10^{14}$, Salez $10^{17}$, Mihnea–Bogdan $10^{18}$) rules out
  counterexamples far beyond our range but exhibits no mechanism.
- **Vaughan (1970)**: exceptional set $\ll x\exp(-c(\log x)^{2/3})$ —
  asymptotically stronger than any fixed power of $\log x$; our chain's
  value is mechanism (explicit certificates, exact criteria, machine-verified
  lemmas), not raw density.
- This project supplies the largest verified certificate dataset
  (to $10^{12}$), exact solvability criteria,
  and the reciprocity structure theory of joint failure.

### Priority audit (August 2026) — what is *not* ours

A literature survey plus four scoping searches settled the attribution
of every headline claim. The findings are now carried in the paper
(Remark 1.7 and the preamble to §5.1); recorded here so they are not
re-discovered:

- **Prop. 1.1 (residual formulation)** — Bradford (Integers 21 (2021)
  #A24). Already credited. López (arXiv:2404.01508) states the
  shift-indexed divisor condition in general form for one solution shape.
- **Thm. 1.2 (R = 3) and Thm. 1.4 (R = 7)** — **Yamamoto (1965), §3**.
  His coverings $\{-s/q\}$ in the system $\Sigma_1$ are exactly our
  criteria: (19) gives R = 3, (20) gives R = 7, and his p. 45 remark
  states the quadratic-residue form explicitly, on precisely the six hard
  classes. Neither theorem covers a single prime he did not. Our earlier
  characterisation of Yamamoto as "a necessary character condition, not a
  solvability criterion" was **wrong** and has been corrected.
- **Thm. 1.5 (R = 11)** — half-anticipated. Yamamoto's Table 3 has the
  three singleton-sufficient classes $q \equiv 7, 8, 10$; the complement
  (classes 2 and 6 outside the budget family) and the exactness are ours.
  413 vs 628 primes certified below $4\cdot10^5$.
- **Thm. 1.6 (R = 15)** — mostly survives. Yamamoto's rules (i)–(ii)
  apply verbatim at s = 15 (he never wrote the case) and give three of the
  four Jacobi classes; the fourth ($q \equiv 11$) and the exactness are
  ours. 315 vs 355 primes.
- **Thm. 1.11 (support theorem)** — as an additive statement this is the
  **critical number** of $\mathbb{Z}/d$: Diderrich–Mann (1973), completed
  for all finite abelian groups by Freeze–Gao–Geroldinger (2009). Our
  contribution is the transport (bounded exponent budgets, single target)
  — and, verified computationally here, the fact that the budget-2 form
  has **no exceptions**, where the classical $\Sigma$-form fails at
  $\mathbb{Z}/4, \mathbb{Z}/6, \mathbb{Z}/8, \mathbb{Z}/2\times\mathbb{Z}/4$
  — i.e. exactly at the admissible residuals R = 7 and R = 15.
- **Thm. 5.8 (branch count $2^{c\sqrt d}$)** — new as stated, classical in
  content: complete-partition counts are $\exp(\Theta(\sqrt n))$
  (Andrews–Beck–Hopkins 1998).
- **Thm. 5.9 (kernel branch)** — the mechanism is the textbook Kneser
  stabilizer/quotient reduction (Grynkiewicz, *Structural Additive
  Theory*, Ch. 6). Now stated as such.
- **Thm. 1.3 (finite reduction)** — no anticipation found, but it is
  bookkeeping on Bradford's criterion and finite-generation statements
  abound (Terzi 1971; Yamamoto §3; Salez). Demoted from "meta-theorem".
- **Thm. 5.5 (uniform chain, R_min ≤ ε log log x)** — survives, but it is
  **not the first almost-all bound on $R_{\min}$**. Vaughan's 1970
  covering congruences are *constructive* and already give
  $R_{\min} \le \exp(O((\log x)^{1/3}))$ outside
  $x\exp(-c(\log x)^{2/3})$. Our content is the *threshold*: a constant
  multiple of $\log\log x$ at comparable exceptional-set quality — an
  exponential gain. The claim "no bound on $R_{\min}$ was previously
  available by any method" was **false** and is gone.
- **Thm. 5.19 (first link sharp)** — Sander (JNT 46 (1994) 123–136) has
  the matching *lower* bound; the accessible evidence (zbMATH review,
  Sander's own 1991 summary) says he states **no** upper bound. The upper
  bound is Fundamental-Lemma folklore and is proved here.
- **Conj. 5.10** — Vu, Combinatorica 30 (2010), does **not** apply: his
  incompleteness structure theorem needs $|A| \ge (5/6+\delta)n/p_1$,
  far above our $d/2 - 1$ regime.

## Theoretical Results (see THEORY.md)

- **Theorem A** (R=3 exact criterion) and **Theorem A′** (R=7, hard primes,
  machine-verified) — proved and verified against all data.
- **Theorem A″** (R=11 exact criterion) — the first case beyond the
  character dichotomy: failure ⟺ all factors QR mod 11, *or* one of three
  explicit exponent-budget patterns (verified on 158 759/158 759 primes).
- **Theorem A‴** (R=15 exact criterion — the first composite residual) —
  a clean *Jacobi-character* dichotomy: residual 15 succeeds ⟺ (p+15)/4
  has a prime factor q with (q|15) = −1 (q ≡ 7, 11, 13, 14 mod 15).
  Zero budget cases (consistency forces non-residue factors in pairs);
  machine-verified over 349 920 consistent configurations and validated
  on 158 759/158 759 sampled primes below 10⁹.
- **Meta-theorem** — every fixed R admits a computable exact finite-state
  criterion (`theory.solvable_exact`, `theory.finite_criterion_dp`); now
  extended to composite R via the unit group (Z/R)*
  (`theory.solvable_exact_general`, exact on every composite residual
  tested against the 10⁹ masks).
- **Theorem E** (unconditional, full proof) — hard primes failing both
  R=3 and R=7 number O(x/(log x)²); empirically density ≈ 5.17/log x,
  constant to 2 % across three decades. With A″, the {3,7,11} exceptional
  set is O(x/(log x)^{5/2}).
- **Theorems F/G/G′/H** (the chain) — joint exceptional sets:
  {3,7,11} → O(x/(log x)^{5/2}); {3,7,11,15} → O(x/(log x)³) (exponent 3
  already at B=15 via A‴); all fifteen primes ≤ 107 → **17/2**; the full
  27-residual admissible list ≤ 107 → **29/2**; and now for **every**
  finite admissible list P (prime or composite): exponent 1 + |P|/2.
- **Theorem S** (unconditional support bound — Kneser/Olson route) —
  the former machine-verified Lemma S is now *proved for every residual
  at once*: if the factor classes of (p+R)/4 occupy ≥ (R−1)/2 nonzero
  classes, every class mod R is a divisor class of m² and R succeeds;
  failure forces support ≤ (R−3)/2. Proof via Kneser's addition theorem
  (stabilizer dichotomy); tight (character-type configurations). General
  abelian form covers composite R (≥ φ(R)/2 classes forbidden for all
  ω(R) ≤ 2). "Lemma S past 107" is thereby closed for all R, and the
  DP verifications 19…107 become independent confirmations.
- **Theorem I** (aggregate identities) — R | p+1 or R | p+4 always
  certifies; the only a-independent families; +1 to the chain (**19/2**
  on the prime list, **31/2** on the full 27-residual list); covers 74 %
  of hard primes alone; characterizes the critical primes.
- **Theorem J** (reciprocity structure) — (q|R) = (p|q) for odd primes
  q | (p+R)/4: joint character failure ⟺ p is a QR mod every unforced prime
  of every shifted value. Describes what a record prime looks like
  mechanically (8 803 369: only 43 distinct odd primes over its 27
  shifted values, 81 % of them with (p|q) = +1 — no significance level
  is attached, since the prime was selected *because* it was the record)
  and explains why the hard classes are the
  squares mod 840 (forced small primes are character-neutral).
- **Theorem K** (conditional; a sketch in THEORY.md §2.9, presented in
  the paper as part of Open Problem 5) — under Dickson's conjecture, every fixed
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
  `reach_sublist`), the full finite verifications of Theorem A′
  (R = 7, 1,536 configurations) and Theorem A″ (R = 11, 497,664
  capped configurations with the exact two-case failure
  classification), and Lemma S at R = 19 and R = 23 (437,580 +
  7,759,752 checks), all via `native_decide` — plus the proved
  discrete-log bridges (`Bridges.lean`): mask semantics as theorems,
  and multiplicative-model forms of A″ and both support bounds, each
  inheriting exactly one evaluator axiom — plus the
  reach ⟺ divisor-certificate bridge (`DivisorBridge.lean`):
  reachability ⟺ ∃ divisor of m² in the class (FTA), and
  `reach_certificate` produces the explicit positive (k, b, c) with
  the ES identity — the meta-theorem's reduction, standard axioms
  only — plus budget-consolidation glue and the composed corollary
  `lemmaS_R19_certificate` (nine distinct nontrivial factor classes
  of (p+19)/4 mod 19 ⟹ explicit solution), and Lemma S at R = 31 via
  certified dynamic programming (`LemmaS31.lean`): the 77.6M supports
  covered through 3,001 states by a machine-checked soundness
  induction; the evaluator runs the DP plus the final 3,001 × 30
  check, with the DP's correctness proved, not trusted. Sorry-free;
  every main theorem axiom-audited, helpers covered transitively; see
  `lean/README.md`.
  Remaining formal roadmap: extend the DP to R = 43+ (state counts
  grow), composed corollaries at other residuals.

## Current Assessment
- No counterexample; all 1 175 215 396 hard primes below $10^{12}$ have
  verified solutions, with $R \le 111$.
- The record's slow growth is *explained* (Theorem J): joint failure is a
  Legendre-coin large-deviation event; expected record growth
  $\asymp \log x/\log\log x$ at the pure-character-type level. The
  plateau at $R = 107$, unbroken over five orders of magnitude, ended at $10^{12}$ with $R = 111$ —
  a move in the direction and roughly on the timescale the model and
  the growth law indicate, not a surprise to be explained away.
- The fixed-finite-list reduction is conditionally **false** (Theorem K):
  the correctly-posed open problem is an unconditional bound on
  $R_{\min}(p)$ — which, by completeness, *is* the conjecture.
- Almost-all coverage is settled with mechanism: exponent 29/2 chain
  (31/2 with the aggregate families),
  exact criteria for R = 3, 7, 11, and per-residual finite-state criteria
  for every fixed R (meta-theorem); and now unconditionally uniform —
  Theorem U gives $R_{\min} \le \varepsilon\log\log x$ outside a set
  of size $x\exp(-c(\log\log x)^2)$, the proved ceiling of the
  method family.

## Next Natural Steps (updated)
1. ~~Extend past $10^8$, $10^9$, $10^{10}$, $10^{11}$, $10^{12}$.~~
   **Done** — the $10^{11}$ run filled the gap with the predicted
   conditional distribution, and the $10^{12}$ run (10.5 h on 32 cores,
   `scripts/run_1e12.sh`) broke the record at $R = 111$, inside the
   forecast window. Next decade ($10^{13}$) costs ~10–20× the $10^{12}$
   run and is the natural next falsifiable test: the same model, now
   with a second record point to calibrate against, should be re-fitted
   before it is used to forecast again.
2. ~~Fixed finite list?~~ **Resolved in direction**: covering lists computed
   (18 suffice below $10^9$, lower bound 12); fixed lists fail infinitely
   often under Dickson (Theorem K). Remaining: nothing short of the
   conjecture itself (completeness).
3. ~~Single fixed $R$ covering an entire hard class?~~ **No** — each
   fixed $R$ has positive-density failure in every class (exact
   criteria + Selberg–Delange); coverage is inherently a union over
   residuals/families.
4. ~~Algebraic conditions forcing large $R$.~~ **Done** — Proposition 1
   (character obstruction), Theorem A″ (budget patterns), Theorem J
   (reciprocity structure): the full mechanism of the tail.
5. ~~Composite-residual criteria (R = 15 first).~~ **Done** — Theorem A‴:
   a clean Jacobi dichotomy, plus the general composite-R exact engine.
   ~~Lemma S past 107.~~ ~~Olson-type additive combinatorics.~~ **Both
   done at once** — Theorem S proves the support bound unconditionally
   for every residual via Kneser's addition theorem; the chain now has
   exponent 1 + |P|/2 for every finite admissible list. Open:
   exploit the subgroup-trapped structure of failing supports
   *uniformly in R* (p-independent branches — the remaining gap on the
   conditionally-past-Vaughan route); formalize Theorem S and A‴ in
   Lean — largely **done**: ladder Lemmas J°/N (`Ladder.lean`), the
   R = 15 product-index bridge (`BridgeR15.lean`, first non-cyclic
   mask bridge), **Theorem S(i) fully symbolic** (`TheoremS.lean`:
   vendored sorry-free Kneser + iterated form + the support bound),
   and the branch layer (`KernelBranch.lean`: Theorem 4.8's kernel
   step with the quotient constructed, the $d/2-1$ container bound,
   Prop 4.12 β-vacuity, and Theorem 4.7's completeness lemma) — all
   on standard axioms only; the three earlier caveats (family
   positivity, Theorem A mod 3, capped configurations) are closed.
   Wave 3 added `Elementary.lean` (Prop 1.1 completeness in both
   directions — the paper's organizing equivalence — plus Props 2.1
   and 2.2), generalized Theorem S to **any finite abelian group
   with an explicit involution count** (paper Thm 1.10(iii); the
   even-cyclic and odd cases are now instances, and the file
   *shrank*), and closed Theorem 4.7 end to end with an explicit
   $2^{c\sqrt d}$ bound. Remaining: Theorem 1.10(ii)'s transfer to
   the multiplicative model, the $t = 2^{\omega(R)}-1$ involution
   count, the iterated reduction; the
   unconditional $R_{\min}$ bound (= the conjecture).

---
*Attack ongoing. Framework and data are ready for further extension or theoretical work.*
