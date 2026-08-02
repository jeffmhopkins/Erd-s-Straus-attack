# Erdős–Straus, Hard Primes: Obstruction Theory for the Residual Method

**Date:** 2026-08-02.
**Status:** Theorems A, A′, and Propositions 1–3 are proved (A′ by
machine-verified finite case analysis, reproducible via
`erdos_straus.theory.verify_R7_finite`). Theorem D is proved modulo standard
sieve machinery, with the dependence stated. Section 6 is heuristic and is
validated against the complete solvability data for all 1 587 581 hard primes
below 10⁹ (`data/analysis/residual_masks_1e9.json.gz`).

---

## 1. Setup and notation

A **hard prime** is a prime in one of the six Mordell classes
{1, 121, 169, 289, 361, 529} mod 840 — the squares of units mod 840. Three
structural facts about hard primes are used repeatedly:

- **(H1)** p ≡ 1 (mod 8);
- **(H2)** p ≡ 1 (mod 3);
- **(H3)** p mod 7 ∈ {1, 2, 4} — a quadratic residue mod 7.

For an admissible residual R (R ≡ 3 mod 4, so that a = (p+R)/4 is an
integer), write

    a = (p+R)/4,   m = p·a,   and the certificate condition:
    ∃ k | m² with k ≡ −m (mod R);  then b = (k+m)/R, c = (m²/k+m)/R.

Two elementary but decisive congruences:

    4a ≡ p (mod R)    ⟹    a ≡ 4⁻¹p,   m ≡ 4⁻¹p²  (mod R).      (∗)

Since gcd(p, R) = 1 (p > R prime), (∗) gives gcd(a, R) = gcd(m, R) = 1
**automatically** — the setting is always "unit" mod R.

Consequence of (∗): **m is a square modulo every prime r | R.** Hence for
every prime r | R with r ≡ 3 (mod 4),

    (−m | r) = (−1 | r)·(m | r) = −1,                            (∗∗)

the target class −m is a quadratic **non**-residue mod r. Every R ≡ 3
(mod 4) has at least one prime factor r ≡ 3 (mod 4).

---

## 2. Proved results

### Proposition 1 (character obstruction)

*Let r | R be prime with r ≡ 3 (mod 4). If every prime factor q of m = p·a
satisfies (q | r) = +1, then residual R fails at p.*

**Proof.** Every divisor k of m² is a product of prime factors of m, hence
(k | r) = +1. A certificate requires k ≡ −m (mod R), so k ≡ −m (mod r),
forcing (k | r) = (−m | r) = −1 by (∗∗) — impossible. ∎

We call a failure of this kind **Type I**. A failure where m *does* have a
non-residue prime factor mod every relevant r, yet no divisor of m² lands in
the exact class −m mod R, is **Type II** (a "class miss").

### Theorem A (exact criterion for R = 3)

*Let p ≡ 1 (mod 4) with 3 ∤ p and a = (p+3)/4. Residual 3 succeeds ⟺ a has
a prime factor q ≡ 2 (mod 3). Explicitly, if q ≡ 2 (mod 3) divides a with
valuation v ≥ 1, then k = q^{2v−1} (or simply k = q) is a certificate.*

**Proof.** Mod 3 the unit group has order 2, so quadratic character *equals*
class: −m ≡ 2 (mod 3) by (∗∗)-type computation (p² ≡ 1, 4⁻¹ ≡ 1, so
m ≡ 1 and −m ≡ 2). *Necessity:* if all prime factors of a are ≡ 1 (mod 3)
(note p ≡ 1 and 3 ∤ a since a ≡ 4⁻¹p ≡ 1), every divisor of m² is ≡ 1,
missing class 2. *Sufficiency:* k = q^{2v−1} ≡ 2^{odd} ≡ 2 (mod 3), and
k | m² since v_q(m²) ≥ 2v. Integrality of b and c is automatic: k ≡ −m gives
3 | k+m, and m²/k ≡ m²(−m)⁻¹ = −m gives 3 | m²/k + m. ∎

Verified against ground truth for **all 1 587 581 hard primes below 10⁹:
1 587 581/1 587 581 agreements, zero exceptions.**

### Theorem A′ (exact criterion for R = 7, hard primes) — NEW

*Let p be a hard prime, a = (p+7)/4. Residual 7 succeeds ⟺ a has a prime
factor that is a quadratic non-residue mod 7 (i.e. ≡ 3, 5, or 6 mod 7).*

**Proof.** (⇐ is the nontrivial direction; ⇒ is Proposition 1 with r = R = 7.)
Success depends only on the multiset of factor classes of m in
(Z/7)* ≅ Z/6: a divisor of m² uses each prime factor with exponent at most
twice its multiplicity, and multiplicities cap at 3 since 2·3 = 6 exhausts a
cycle. The configuration space is therefore finite. Three structural
constraints cut it down:

1. p mod 7 ∈ {1, 2, 4} — by (H3);
2. **2 | a** — by (H1): p ≡ 1 (mod 8) ⟹ p + 7 ≡ 0 (mod 8) ⟹ a even. So
   the class of 2 (a QR mod 7) is always present among a's factors;
3. the factor classes multiply to a ≡ 4⁻¹p (mod 7), by (∗).

An exhaustive check of all **1536** consistent configurations
(`theory.verify_R7_finite`) confirms: the target class −m is realizable by a
bounded-exponent subproduct precisely when some factor is a non-residue. ∎

**Remark (why the hard classes matter).** For general p ≡ 1 (mod 4) the
statement is FALSE: e.g. p = 701, a = 177 = 3·59 has the non-residue factor
3, yet R = 7 fails (verified). The rescue for hard primes is exactly the
forced factor 2 from (H1) together with (H3) — the mod-8 structure of the
Mordell classes feeds into the mod-7 divisor problem. Empirically this
theorem manifests as: **41 421 out of 41 421 sampled R=7 failures are
Type I** — R=7 never fails by class miss on hard primes.

### Proposition 3 (guaranteed-success classes)

*Let t = −4⁻¹p² mod R. If a has a prime factor q with q ≡ t·p^{−i} (mod R)
for some i ∈ {0, 1, 2}, then k = q·pⁱ is a certificate. In particular
t·p⁻² ≡ −4⁻¹ (mod R) is a "universal" success class independent of p:
any prime factor of a in class −4⁻¹ mod R certifies success.*

**Proof.** k = q·pⁱ divides m² (q | a, i ≤ 2) and lies in class
t·p^{−i}·pⁱ = t = −m. ∎

*Contrapositive (sieve form):* failure at R ⟹ (p+R)/4 has **no prime factor
in the ≤ 3 classes S_R(p) = {t, tp⁻¹, tp⁻²} mod R** — a sifting condition of
dimension κ_R ≥ |S_R(p)|/φ(R) ≥ 1/φ(R) on the shifted linear form
(p+R)/4. Validated: **zero violations across every residual tested** on the
10⁹ mask data.

### Theorem B (finite covering reduction; refined statement)

For each admissible R let D_R(p) ⊂ (Z/R)* be the set of classes of divisors
of m² — the set of **bounded-exponent subproducts** ∏ q_j^{e_j}, e_j ≤ 2·v_j,
of the factor classes of m. Call R *admissible for p* if −m mod R ∈ D_R(p).

*If a finite set S of admissible residuals has the property that every hard
prime admits some R ∈ S with −m mod R ∈ D_R(p), then the Erdős–Straus
conjecture holds for all hard primes, hence for all n ≥ 2. The reduction is
constructive: testing membership requires factoring (p+R)/4 for R ∈ S.*

**Refinement note.** An earlier formulation used the *monoid* generated by
the factor classes; that is too generous — divisors of m² carry bounded
exponents, and monoid membership with an exponent beyond the budget need not
be realizable (exponents can only be reduced modulo ord_R(q) when they
exceed a full cycle). D_R(p) as defined is exactly what the computation
verifies. The computational statement stands: **S₀ = {3, 7, 11, …, 107}
(all R ≡ 3 mod 4) satisfies the hypothesis for every hard prime below 10⁹.**

### Theorem C/D (density of exceptions; quantitative)

*(C, R = 3.) The hard primes for which residual 3 fails have relative density
zero: their count up to x is O(x/(log x)^{3/2}), i.e. a proportion
O((log x)^{−1/2}) of hard primes.*

**Proof sketch.** By Theorem A the failing set is {p : (p+3)/4 has no prime
factor ≡ 2 (mod 3)}. Sifting the linear form (p+3)/4 by the primes
q ≡ 2 (mod 3) (half of all primes: sieve dimension κ = 1/2) with a
Brun–Selberg upper-bound sieve gives the count. Note the naive argument
"integers free of class-2 factors have density zero, hence so does the
preimage" is insufficient — primes are already density zero; the sieve on
the shifted form is what makes the statement legitimate. The same argument
applies verbatim to R = 7 via Theorem A′. ∎

*(D, general.) For every A > 0 there is a finite admissible set S(A) such
that the number of hard primes p ≤ x with every residual in S(A) failing is
O_A(x/(log x)^{1+A}).*

**Proof sketch.** By Proposition 3, failure at R implies the form (p+R)/4
avoids prime factors in ≥ 1 explicit class mod R. Distinct R give distinct
shifts — a system of linear forms, sifted simultaneously with total
dimension κ(S) = Σ_R κ_R ≥ Σ_R 1/φ(R). Since Σ_{R ≡ 3 (4)} 1/φ(R) diverges,
κ(S) can be made > A with a finite S; the multidimensional Selberg sieve
(Halberstam–Richert) yields the bound. ∎

Theorem D is the strongest rigorous statement short of finiteness: residual
shells capture all hard primes except a set of relative density
O((log x)^{−A}) **for every A** — but the sieve cannot by itself close the
gap to *all* primes, which is exactly the content of the finite covering
hypothesis in Theorem B.

---

## 3. Empirical validation at 10⁹

All statements tested against the complete per-prime solvability masks
(27 residuals × 1 587 581 hard primes).

| Claim | Test | Result |
|---|---|---|
| Theorem A (R=3 iff) | all 1 587 581 primes | exact, 0 disagreements |
| Theorem A′ manifests as pure Type I | 41 421 sampled R=7 failures | 100 % Type I, 0 Type II |
| Prop 1 direction | classifier consistency | ✓ |
| Prop 3 (no factor in S_R(p) among failures) | every residual tested | 0 violations |
| κ = 1/2 decay for R=7 (Thm A′ + sieve) | binned fit | κ̂ = 0.539 |
| κ = 1/2 decay for R=3 | binned fit | κ̂ = 0.387 (short range; S–D lower-order terms) |

Type I share of failures by residual (sampled): R=7: 100 %, R=23: 96.6 %,
R=11: 89.7 %, R=47: 87.2 %, R=71: 82.1 %, R=31: 79.3 %, … down to
R=67: 33.5 %. Character obstruction dominates at residuals that are prime
or have small 3-mod-4 prime power structure; class misses (Type II) grow
with φ(R) — as expected, since hitting one specific class among φ(R) gets
harder while the character argument only sees the QR/NQR dichotomy.

---

## 4. The four critical primes

Exactly 4 of 1 587 581 primes have a *unique* working residual ≤ 107 — the
entire obstruction to a shorter covering list, one per hard class involved:

| p | unique R | p mod 840 | failure anatomy (26 failures) |
|---:|---:|---:|---|
| 8 803 369 | 107 | 169 | 12 Type I + 14 Type II |
| 142 361 209 | 59 | 529 | 13 Type I + 13 Type II |
| 287 567 281 | 83 | 1 | 13 Type I + 13 Type II |
| 794 037 841 | 63 | 121 | 16 Type I + 10 Type II |

The record prime p = 8 803 369 fails every residual below 107 **even
allowing R up to 400**; its a-values are anomalously smooth (at R = 107,
a = 3²·11²·43·47). Its escape requires both failure mechanisms in roughly
equal measure — it is not explained by the character obstruction alone, nor
by class misses alone.

---

## 5. The distribution of minimal R and the gap {87, …, 103}

Minimal-R distribution at 10⁹: R=3 covers 49.1 %, {3,7,11} covers 91.3 %,
R ≤ 23 covers 99.3 %. Full histogram in `data/analysis/dist_1e9.json`.

**The gap needs no modular explanation.** Under the independence model
(Section 6), expected counts of primes with minimal R = 87, 91, 95, 99, 103
are 0.12, 0.03, 0.05, 0.01, 0.01 — all ≪ 1. Observing zero in each is the
default outcome. The same model reproduces the observed counts at
R = 75, 79, 83 (expected 0.28, 0.39, 0.17; observed 2, 1, 2) up to the
correlation factor discussed below.

**The record is the anomaly, not the gap.** Conditioned on a prime failing
every residual ≤ 83, the independence model gives it a 53 % chance of
landing at minimal R = 87 and only a 1.7 % chance of landing at 107. The
one deep-tail prime below 10⁹ landed at 107. Together with the smoothness of
its a-values, this marks the record prime as structurally atypical even
among deep-tail primes — consistent with strong positive correlation of
failures across residuals for primes with smooth shifted values.

---

## 6. Independence model, correlations, and the 10¹⁰ forecast

Model: P(min R > B) = Π_{R ≤ B} f_R, with marginal failure rates f_R
measured from the masks. In-sample calibration:

| B | expected # (indep.) | observed |
|---:|---:|---:|
| 23 | 8 086 | 10 865 |
| 47 | 72.5 | 158 |
| 83 | 0.33 | 1 |
| 103 | 0.03 | 1 |

The observed/expected ratio rises from ≈1.3 (B=23) to ≈30 (B=103):
failures at different residuals are **positively correlated**, increasingly
so down the tail (shared mechanisms: smoothness of p+R over nearby shifts;
QR conditions mod common prime factors r of different R; 12 of the 27
residuals share the factor 3).

**Forecast for the decade [10⁹, 10¹⁰]** (~12.6 M hard primes), using fitted
power laws f_R(x) = C_R (log x)^{−κ_R}:

- new primes with min R > 83: ≈1.1 expected (indep.) × correlation ≈ 3 ⟹
  **a few expected**;
- new primes with min R > 107 (record broken): 0.038 (indep.);
  with the ×30 deep-tail calibration ⟹ **order 1 — a genuine coin flip**.

Both are sharp, falsifiable predictions of the model; the 10¹⁰ run tests
them directly.

---

## 7. Covering sets at 10⁹

- Occurring minimal residuals: 22 values
  {3, 7, …, 83} ∪ {107} (all R ≡ 3 mod 4 up to 83, plus 107).
- Smallest covering list found (greedy over full masks): **18 residuals** —
  {3, 11, 15, 19, 23, 31, 39, 47, 59, 63, 71, 79, 83, 87, 95, 99, 103, 107};
  restricting candidates to the 22 occurring values also yields an
  18-element cover.
- Rigorous lower bound via disjoint-mask packing: **12** (12 primes with
  pairwise disjoint option sets exhibited). True optimum ∈ [12, 18].

---

## 8. What would close the hard cases

1. **Finite covering (Theorem B hypothesis).** Prove some finite S works for
   all hard primes. The sieve (Theorem D) gives density-(log x)^{−A}
   exceptional sets for every A but cannot reach emptiness.
2. **More exact criteria.** R = 3 and R = 7 now have exact factor-class
   criteria. The same finite-verification method applies to any fixed R
   (configuration space (Z/R)* with capped multiplicities) — each new exact
   criterion converts a residual's failure set into an explicit
   multiplicative sieve condition. R = 11 already exhibits genuine Type II
   failures, so its criterion must go beyond the character dichotomy —
   the first structurally new case.
3. **Understand deep-tail correlation.** The ×30 calibration factor says
   smooth-shift primes fail *jointly*. A quantitative model of
   P(fail at R | a_R smooth) would turn the record forecast into a theorem-
   grade tail bound and possibly explain why records are so static.

---

## Appendix: reproduction

```bash
# full battery (Theorem A validation, taxonomy, fits, model, critical primes)
python -m erdos_straus.theory --masks data/analysis/residual_masks_1e9.json.gz

# Theorem A' finite verification alone (fast)
python -c "from erdos_straus.theory import verify_R7_finite; print(verify_R7_finite())"
```
