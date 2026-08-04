# Erdős–Straus, Hard Primes: Obstruction Theory for the Residual Method

> **Attribution notice (August 2026).** A priority audit established
> that several results developed below are anticipated in the
> literature — most importantly the exact criteria at R = 3 and R = 7
> (Yamamoto 1965, §3), the support theorem as an additive statement
> (Diderrich–Mann 1973; Freeze–Gao–Geroldinger 2009), the kernel-branch
> reduction (standard Kneser stabilizer/quotient argument), and the fact
> that Vaughan's 1970 covering congruences are constructive and hence
> already yield an almost-all bound on R_min. **Read the "Priority
> audit" section of STATUS.md alongside this document**; where the two
> disagree on what is new, STATUS.md and the paper are current and this
> file is historical.

**Date:** 2026-08-04 (current through PR #58 — the $10^{12}$ census, in
which the record R = 107 — unmoved over five orders of magnitude — breaks at **R = 111**, inside the
decade §6's calibrated model had named; see §5 and §6. Earlier: this
revision adds
Theorem S and Theorem A‴; §2.10 adds the Burgess/reciprocity
route, its full-population census and failure anatomy, the
ladder theorems L₀ (rigorous, fixed length) and L₁ (almost-all,
conditional on the measured Hypothesis B), Theorem B₁ (proved),
Theorems B₂ and P₁ (proof sketches), and Hypothesis P with
Corollary B₃ — **PR #56 corrects P₁**, which was false as stated
(its admissibility test ignored the small primes the class forces to
divide a), replacing it by paper Theorem 5.8 with the completed local
conditions, and adds the two results the correction produced: the
norm-form bridge (paper eq. (5.1)) and the sharpness of the first link
(paper Theorem 5.7, failures at R = 3, 7, 15 are ≍ x/(log x)^{3/2},
with 3/2 the ceiling of the whole method); §2.11 adds **Theorem U** — the unconditional uniform
chain, R_min ≤ ε·log log x for all but x·exp(−c(log log x)²) hard
primes — the ceiling analysis, and the two obstruction lemmas
closing the pretension and almost-prime routes; §2.12 adds the
branch classification: Theorem M-kernel proved, the count form
refuted, **Conjecture A** (window containers) with exhaustive
verification for every modulus d ≤ 30 and at nine larger moduli, and the conditional polylog tier
R_min ≤ (log x)^{c₀}).  
**Status:** Proved: Theorems A, A′, A″, A‴ (exact criteria for
R = 3, 7, 11, and now the first composite residual R = 15; A′/A″/A‴ by
machine-verified finite case analysis), the meta-theorem (now including
composite R), Propositions 1 (now in composite/Jacobi form) and 3,
Theorem E and the chain F/G/G′/H, **Theorem S** — the support bound
(formerly "Lemma S") proved unconditionally for EVERY residual via
Kneser's addition theorem, with no upper limit and composite residuals
included, upgrading the chain to arbitrary finite residual lists
(exponent 29/2 for the full 27-residual list ≤ 107; 31/2 with the
two aggregate identity families adjoined) — Theorem I
(aggregate families), Theorem J (reciprocity structure), Theorem D
(full proof in the paper), Theorem B₁ (the ladder's first rung,
§2.10), and **Theorem U** (the uniform chain, §2.11 — the strongest
unconditional statement of the development). Theorem K is a
conditional sketch under
Dickson's conjecture. Section 6 is heuristic, validated against the
complete solvability data below 10⁹ and the 10¹⁰/10¹¹/10¹² minimal-R
data.
§2.8 records two executed attempts at totality and their
precisely-characterized walls; the completeness proposition (paper
Prop. 1.1: R_min ≤ 2p ⟺
ESC) calibrates what "closing the problem" requires. Much of the
elementary and enumeration layer is machine-checked in Lean 4
(`lean/README.md`); paper counterparts of each named result are listed
in the mapping table below.

## Provenance note (added PR #56)

Proposition 1.1 (completeness) is **not new**: the bounded search
space together with the divisor-congruence criterion mod 4a − p is
Bradford's (Integers 21 (2021) #A24, arXiv:1906.00561), now commonly
called the Bradford conditions; his denominator range is slightly
sharper than ours. The earlier framing in this file and in the paper
overstated the novelty of the formulation, and the claim that "no
bound on R_min was previously available" was wrong — Bradford's
search space gives R_min(p) ≪ p. What this development adds is the
residual-indexed program built on the criterion (exactness at fixed
R, reciprocity across residuals, the uniform support theorem) and the
bounds on R_min of smaller order that follow from it.

## Name mapping to the paper

This document uses working letter names; the paper numbers results.
The dictionary (paper labels in parentheses):

| here | paper |
|---|---|
| completeness observation | Proposition 1.1 (`prop:complete`) |
| Proposition 1 (character obstruction) | Proposition 2.1 (`prop:char`) |
| Proposition 3 (guaranteed success) | Proposition 2.2 (`prop:succ`) |
| Theorem A / A′ / A″ | Theorems 1.2 / 1.4 / 1.5 |
| Theorem A‴ (R = 15, composite) | Theorem 1.6 (`thm:R15`) |
| meta-theorem | Theorem 1.3 (`thm:meta`) |
| Theorem B (finite covering reduction) | Remark 4.4 (unlabeled in source) |
| Theorem C | not carried into the paper |
| Theorem D (density reduction) | Theorem 1.13 (`thm:D`) |
| Theorems E/F/G/G′/H (the chain) | the single Theorem 1.11 (`thm:FG`) (G/G′ use the legacy lists {3,7,11,19}/{3,7,11,19,23}; the paper's chain runs {3,7}, {3,7,11}, {3,7,11,15}, {3,7,11,15,19}) |
| Theorem I (aggregate families) | Proposition 1.12 (`prop:agg`) |
| Theorem J (reciprocity) | Theorem 1.8 (`thm:J`) |
| Corollaries J1/J2 | Corollary 2.3(i)/(ii) (`cor:J`) |
| Theorem K (conditional) | sketch inside Open Problem 5 |
| Lemma S (support bound) | Lemma 1.9 (`lem:S`) |
| Theorem S (unconditional support bound, Kneser) | Theorem 1.10 (`thm:S`) |
| Lemma J° (composite reciprocity) | Lemma 5.1 (`lem:Jcomp`) |
| Lemma N (Jacobi necessity) | Lemma 5.2 (`lem:N`) |
| Theorem L₀ (ladder chain) | Theorem 5.3 (`thm:L0`) |
| Theorem B₁ (first rung) | Theorem 5.4 (`thm:B1`) |
| Theorem B₂ (proxy ladder) | Theorem 5.5 (`thm:B2`) |
| Hypothesis P / Hypothesis B | Hypotheses 5.6 / 5.10 |
| Corollary B₃ (second rung under P) | the unnumbered display following Hypothesis 5.6 |
| the norm-form bridge (all factors QR mod r ⟺ primitive representation by a form of discriminant −r) | equation (5.1) (`eq:normform`) |
| the sharp first link (failures at R = 3, 7, 15 are ≍ x/(log x)^{3/2}; 3/2 is the ceiling) | Theorem 5.7 (`thm:sharp`) |
| Theorem P₁ (ladder failure lower bound; **corrected** — the old "half-dimensional failures" statement was false, see §2.10) | Theorem 5.8 (`thm:P1`) |
| scope of Theorem 5.8 (availability 0.023 %, vacuity counterexample, one-sided bracket off the sparse family) | Remark 5.9 (`rem:P1scope`) |
| Theorem L₁ (conditional almost-all) | Theorem 5.11 (`thm:L1`) |
| Lemma Q (least non-residue) | not carried into the paper (used unnamed in the proof of Theorem 5.11) |
| Hypothesis L (ladder) | not carried into the paper |
| Theorem U (uniform chain) | Theorem 4.5 (`thm:U`) |
| the ceiling | Remark 4.6 (`rem:ceiling`) |
| Obstructions (i)/(ii) | Remark 5.13 (`rem:obstruction`) |
| count blow-up | Theorem 4.7 (`thm:Mcount`) |
| Theorem M-kernel (lossless reduction) | Theorem 4.8 (`thm:Mkernel`) |
| Conjecture A (window containers) | Conjecture 4.9 (`conj:A`) |
| container theorem (under A) | Theorem 4.10 (`thm:Mcont`) |
| polylog tier (under A) | Theorem 4.11 (`thm:Upay`) |
| monotonicity reduction | Lemma 4.1 (`lem:mono`) |

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

Since gcd(p, R) = 1 (R ≡ 3 ≢ 1 ≡ p (mod 4), so R ≠ p and p ∤ R),
(∗) gives gcd(a, R) = gcd(m, R) = 1
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

We call a failure of this kind **character-type**. A failure where m *does* have a
non-residue prime factor mod every relevant r, yet no divisor of m² lands in
the exact class −m mod R, is **budget-type** (a "class miss").

### Theorem A (exact criterion for R = 3)

*Let p ≡ 1 (mod 4) with 3 ∤ p and a = (p+3)/4. Residual 3 succeeds ⟺ a has
a prime factor q ≡ 2 (mod 3). Explicitly, if q ≡ 2 (mod 3) divides a with
valuation v ≥ 1, then k = q^{2v−1} (or simply k = q) is a certificate.*

**Proof.** Mod 3 the unit group has order 2, so quadratic character *equals*
class: −m ≡ 2 (mod 3) by (∗∗)-type computation (p² ≡ 1, 4⁻¹ ≡ 1, so
m ≡ 1 and −m ≡ 2). *Necessity:* if all prime factors of a are ≡ 1 (mod 3),
then a ≡ 1 (mod 3), hence p = 4a − 3 ≡ 1 (mod 3) as well, so every prime
factor of m = pa is ≡ 1 (mod 3) and every divisor of m² is ≡ 1,
missing class 2. *Sufficiency:* k = q^{2v−1} ≡ 2^{odd} ≡ 2 (mod 3), and
k | m² since v_q(m²) ≥ 2v. Integrality of b and c is automatic: k ≡ −m gives
3 | k+m, and m²/k ≡ m²(−m)⁻¹ = −m gives 3 | m²/k + m. ∎

Verified against ground truth for **all 1 587 581 hard primes below 10⁹:
1 587 581/1 587 581 agreements, zero exceptions.**

### Theorem A′ (exact criterion for R = 7, hard primes)

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
character-type** — R=7 never fails by class miss on hard primes.

### Proposition 3 (guaranteed-success classes)

*Let t = −4⁻¹p² mod R. If a has a prime factor q with q ≡ t·p^{−i} (mod R)
for some i ∈ {0, 1, 2}, then k = q·pⁱ is a certificate. In particular
t·p⁻² ≡ −4⁻¹ (mod R) is a "universal" success class independent of p:
any prime factor of a in class −4⁻¹ mod R certifies success.*

**Proof.** k = q·pⁱ divides m² (q | a, i ≤ 2) and lies in class
t·p^{−i}·pⁱ = t = −m. ∎

*Contrapositive (sieve form):* failure at R ⟹ (p+R)/4 has **no prime factor
in the ≤ 3 classes S_R(p) = {t, tp⁻¹, tp⁻²} mod R** — a sifting condition of
dimension κ_R = t_R/φ(R) ≥ 1/φ(R) (t_R = |S_R(p)|) on the shifted linear
form (p+R)/4. Validated: **zero violations across every residual tested** on the
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
verifies. The computational statement, **updated at 10¹²**:
**S₀ = {3, 7, 11, …, 111} (all R ≡ 3 mod 4) satisfies the hypothesis for
every hard prime below 10¹²** (complete per-residual solvability masks
verified below 10⁹; minimal-R data to 10¹²). The shorter list ending at
107 satisfied it through 10¹¹ but **not** through 10¹²: three primes —
119 945 383 009, 654 730 707 409, 761 403 297 769 — fail every
admissible R ≤ 107 and are certified only at R = 111. This is exactly
the behaviour Theorem K predicts of any fixed list under Dickson's
conjecture, observed once. The paper (Remark 4.4) states the implication
in this direction only: a finite covering set would imply the conjecture
for hard primes, while the conjecture itself bounds R_min(p) by 2p and
does not produce a uniform finite S.

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
dimension κ = 1 + Σ_R t_R/φ(R) ≥ 1 + Σ_R 1/φ(R) (the +1 is the form
4n−3 being prime). Since Σ_{R ≡ 3 (4)} 1/φ(R) diverges, κ can be made
> 1 + A with a finite S; the multidimensional Selberg sieve
(Halberstam–Richert) yields the bound. ∎

Theorem D is the strongest rigorous statement short of finiteness: residual
shells capture all hard primes except a set of relative density
O((log x)^{−A}) **for every A** — but the sieve cannot by itself close the
gap to *all* primes, which is exactly the content of the finite covering
hypothesis in Theorem B.

---

### 2.5 Theorem E ({3,7} covering, unconditional): full proof

**Theorem E.** *The number of hard primes p ≤ x for which residual 3 and
residual 7 both fail is O(x/(log x)²). Consequently all but a proportion
O(1/log x) of hard primes are solved with R ∈ {3, 7}.*

**Proof.**

*Step 1 (exact criteria).* Let p be a hard prime and put n = (p+3)/4, so
that (p+7)/4 = **n + 1** — the two shifted forms are consecutive integers.
By Theorem A, residual 3 fails iff every prime factor of n is ≡ 1 (mod 3).
By Theorem A′, residual 7 fails iff every prime factor of n+1 is a quadratic
residue mod 7 (≡ 1, 2, 4 mod 7). Both criteria are exact, so the
exceptional set is *precisely*

    E(x) = { hard p ≤ x :  n has no prime factor ≡ 2 (mod 3)
                       and n+1 has no prime factor ≡ 3, 5, 6 (mod 7) },
    with p = 4n − 3.

*Step 2 (congruence bookkeeping).* Fix one of the six hard classes h mod
840; then n ≡ (h+3)/4 (mod 210) is a fixed class, and the conditions at the
primes 2, 3, 5, 7 are determined by it (in particular 3 ∤ n, 7 ∤ (n+1)
automatically — §1). It suffices to bound the count in one class and sum
over six.

*Step 3 (containment in a sifted set).* Let z = x^{1/10}. Discarding the
O(z) primes p ≤ z, every p ∈ E(x) yields n ≤ (x+3)/4 with n ≡ n₀ (mod 210)
such that for **every** prime q with 7 < q ≤ z:

    (a) q ≡ 2 (mod 3)  ⟹  n ≢ 0 (mod q);
    (b) q ≡ 3, 5, 6 (mod 7)  ⟹  n ≢ −1 (mod q);
    (c) q ∤ 4n − 3   (since 4n − 3 = p is prime and p > z).

Indeed (a), (b) restate "no prime factor ≤ z in the forbidden classes" —
weaker than the full criteria, which is fine for an upper bound.

*Step 4 (sieve of dimension 2).* This is a standard upper-bound sieve for
the three linear forms n, n+1, 4n−3 with sifting function

    ω(q) = 1_{q ≡ 2 (3)} + 1_{q NQR (7)} + 1        (q > 7),

forbidden classes 0, −1, 3·4⁻¹ mod q, pairwise distinct for q ∤ 21. By
Dirichlet, ω has average value κ = ½ + ½ + 1 = 2 over primes (in the
Halberstam–Richert sense Σ_{q ≤ w} ω(q) log q / q = κ log w + O(1)). The
Fundamental Lemma of sieve theory (e.g. Halberstam–Richert Thm 2.5, or
Friedlander–Iwaniec, Opera de Cribro, Ch. 6) with sifting range
z = x^{1/10} gives

    |E(x)|  ≪  x · Π_{7 < q ≤ z} (1 − ω(q)/q)
            ≍  x · Π_{q≤z}(1 − 1/q) · Π_{q ≡ 2(3), q≤z}(1 − 1/q)
                 · Π_{q NQR(7), q≤z}(1 − 1/q)
            ≍  x · (log z)^{−1} · (log z)^{−1/2} · (log z)^{−1/2}
            =  x (log z)^{−2}  ≍  x (log x)^{−2},

using Mertens' theorem and its arithmetic-progression form. ∎

**Empirical confirmation.** The proportion of hard primes failing both
residuals should decay as C/log x. Measured from the complete 10⁹ masks, the
product (relative density) × (log x) is constant to within 1 % across three
decades:

| bin (p) | rel. density of joint failure | × log x |
|---|---:|---:|
| ~10⁶ | 0.354 | 5.14 |
| ~10⁷ | 0.327 | 5.19 |
| ~6×10⁷ | 0.300 | 5.18 |
| ~2.5×10⁸ | 0.277 | 5.17 |
| ~10⁹ | 0.258 | 5.16 |

i.e. **density(joint {3,7} failure) ≈ 5.17 / log x** — the sieve exponent is
exactly right, and 5.17 estimates the (conjectural) Selberg–Delange
constant. Overall 421 405 of 1 587 581 hard primes below 10⁹ (26.5 %) fail
both — all of them settled by the deeper residuals of S₀.

**Remark (extension).** Each further residual with an exact criterion
contributes its own sifting density on the shifted form (p+R)/4; with the
Prop-3 relaxation alone, every additional R contributes ≥ 1/φ(R)
unconditionally (Theorem D). Theorem E is the fully-worked two-form case.

---

### 2.6 The meta-theorem and the exact criteria for R = 11 and 15

#### Meta-theorem (finite-state exact criteria)

*For every fixed prime R ≡ 3 (mod 4), success of residual R at a hard prime
p depends only on (i) the multiset of classes mod R of the prime factors of
a = (p+R)/4 with multiplicities capped at ⌈(R−1)/2⌉, and (ii) p mod R.
Hence an exact solvability criterion exists for every R and is computable by
finite enumeration.*

**Proof.** A certificate is a divisor k | m² with k ≡ −m (mod R). The set of
divisor classes is determined by the factor classes with exponents capped at
twice the multiplicities; exponents matter only modulo ord_R(class) ≤ R−1,
so multiplicities beyond ⌈(R−1)/2⌉ are equivalent. The target −m ≡ −4⁻¹p²
and the consistency relation Π(classes) = a ≡ 4⁻¹p are functions of
p mod R. ∎

The criterion is implemented directly (`theory.solvable_exact`) — success
decided from factor classes alone, no divisor search — and agrees with
ground truth on every prime tested (R = 11, 19, 23; 7 938 primes each).
Theorems A and A′ are the cases R = 3, 7, where the criterion collapses to
the character dichotomy. The DP enumeration (`theory.finite_criterion_dp`)
compresses each R's configuration space to a handful of equivalence states:
R = 7 with the forced even factor has 4 reachable states (3 success /
1 all-even-fail — Theorem A′ re-derived), R = 11 has 25.

#### Theorem A″ (exact criterion for R = 11, hard primes)

Note first that for every hard prime, at R = 11: **3 | a** (from p ≡ 1 mod 3,
11 ≡ 2 mod 3), a is odd, and 7 ∤ a. The quadratic residues mod 11 are
{1, 3, 4, 5, 9}; note 6 = 2⁻¹ (mod 11).

*Residual 11 fails at a hard prime p ⟺ one of:*

*(a) — character obstruction: every prime factor of a = (p+11)/4 is a QR
mod 11; or*

*(b) — budget obstruction: v₃(a) = 1, every other prime factor of a is
≡ 1 (mod 11) except for a non-residue part w of exactly one of three shapes,
matched to the class of p:*

| non-residue part of a | p mod 11 |
|---|---|
| one prime ≡ 2 (mod 11), multiplicity 1 | 2 |
| one prime ≡ 6 (mod 11), multiplicity 1 | 6 |
| one prime ≡ 2 and one ≡ 6, multiplicity 1 each | 1 |

**Verification:** the criterion agrees with ground truth for **158 759 out of
158 759** hard primes tested (every 10th prime below 10⁹). The DP
enumeration proves cases (a)/(b) are exhaustive: of the 25 equivalence
states, 16 succeed, 6 fail by (a), 3 fail by (b), and — remarkably —
**no state fails by a proper-subgroup obstruction**: in discrete-log
coordinates, the only proper subgroup of Z/10 containing an odd element
is {0, 5}, and the consistency relation forces p's class to extend it to
all of Z/10.

**Structure of (b).** The failing patterns are exponent-budget edge cases:
the only odd-log contributions available are ±1 (single copies of classes
2^{±1}), and with v₃(a) = 1 the even-log contributions are too sparse to
bridge the last step to the target. Any of: v₃(a) ≥ 2, a factor in class
{4, 5, 9}, or a second factor in class 2 or 6 — expands the reachable set
and restores solvability. Sieve-theoretically, case (b) demands all factors
in 4 of the 10 unit classes (dimension 6/10), strictly sparser than case
(a) (dimension 5/10): budget failures are asymptotically negligible within
the failure set, matching their observed ≈10 % share.

**Consequence for Theorem E.** With A″ exact, the joint failure of
{3, 7, 11} is again a fully explicit multiplicative condition on three
forms n, n+1, and (p+11)/4 = n + 2 — **three consecutive integers** — and
the sieve dimension rises to 1 + ½ + ½ + ½ = 5/2 (up to the negligible
(b)-part):  hard primes needing R > 11 number O(x/(log x)^{5/2}), all but
O((log x)^{−3/2}) proportionally.

#### Theorem A‴ (exact criterion for R = 15 — the first composite residual)

For composite R the certificate condition k ≡ −m (mod R) couples the
prime-power components of R through CRT, and the divisor-class group is
the (generally non-cyclic) unit group (Z/R)\*. The meta-theorem holds
verbatim with (Z/R)\* in place of the cyclic group
(`theory.solvable_exact_general` — validated against ground truth on
**every** composite residual in the 10⁹ masks, 7 938 sampled primes per
residual, zero disagreements). Two structural facts single out R = 15:

- **(Jacobi obstruction — Proposition 1, composite form.)** m ≡ (2⁻¹p)²
  (mod R) is the square of a unit, so the *Jacobi* symbol (m|R) = +1;
  and (−1|R) = −1 for every R ≡ 3 (mod 4). Hence (−m|R) = −1: if every
  prime factor of m has (q|R) = +1, every divisor of m² has Jacobi
  symbol +1 and residual R fails. For composite R this is strictly
  stronger than Prop. 1 at a single prime r | R.
- For hard primes at R = 15: p mod 15 ∈ {1, 4} (from p ≡ 1 mod 3,
  p ≡ ±1 mod 5), **2 | a** (p ≡ 1 mod 8 ⟹ 8 | p+15), the target is
  −m ≡ 11 (mod 15) for both p-classes, and consistency reads
  ∏(classes) ≡ 4p (mod 15).

*Theorem A‴. Let p be a hard prime, a = (p+15)/4. Residual 15 succeeds
⟺ a has a prime factor q with (q|15) = −1, i.e. q ≡ 7, 11, 13, or 14
(mod 15).*

**Proof.** Necessity is the Jacobi obstruction: the residue classes
{1, 2, 4, 8} = ⟨2⟩ mod 15 are exactly the units with (q|15) = +1, a
subgroup containing p's class; if all factors lie in it, so does every
divisor of m², missing 11. Sufficiency is a machine-verified finite case
analysis (`theory.verify_R15_finite`): of the **349 920** consistent
configurations, **349 380 succeed and 540 fail — and every failing
configuration is all-residue**. There are **zero budget failures**, in
contrast to R = 11: the consistency relation forces χ₁₅(a) = χ₁₅(4p) =
+1, so non-residue factors occur with *even* total multiplicity, and any
two non-residue units (or one squared), combined with the forced powers
of 2, reach the target. ∎

Validated against ground truth for **158 759 out of 158 759** hard
primes below 10⁹ (every 10th): zero disagreements.

**Remark (a cleaner dichotomy than R = 11).** The first composite
residual turns out to be *simpler* than the last prime one: a pure
character dichotomy — with the quadratic character mod r replaced by the
Jacobi character mod 15 — and no exponent-budget edge cases at all. The
failure condition "no factor in 4 of the 8 unit classes" is a single
sifting branch of dimension exactly ½ on the form (p+15)/4 = n + 3.

**Consequence for the chain.** With A/A′/A″/A‴, joint failure of
{3, 7, 11, 15} is an explicit multiplicative condition on **four
consecutive integers** n, n+1, n+2, n+3 (n = (p+3)/4), a five-form
sieve problem of dimension 1 + 4·(1/2) = 3: hard primes with
R_min > 15 number O(x/(log x)³) — exponent 3 already at B = 15,
which previously required B = 19.

---

### 2.7 The chain: Theorem S, Theorems F/G/G′/H, Theorem I (exponents 5/2 … 31/2)

The exponent bookkeeping to keep straight: each residual with an
exact-criterion-grade handle contributes sifting density **½** (its failure
forbids half the unit classes on its shifted form), and primality of
p = 4n − 3 contributes 1. Three residuals therefore give dimension 5/2 —
**not 3**; exponent 3 requires a fourth residual. The results below are
fully proven.

#### Theorem S (the support bound, proved unconditionally for EVERY residual — the Kneser/Olson route)

What was "Lemma S" — machine-verified one residual at a time, stalled at
R = 107 by DP state growth — is in fact a theorem of additive
combinatorics, valid for every residual at once. This is precisely the
"Olson-type" input anticipated in §2.9(i); the tool is **Kneser's
addition theorem**.

Note the check deliberately ignores the consistency relation
∏(classes) ≡ 4⁻¹p: it examines a *superset* of the realizable
configurations and can only overstate the failing supports — the lemma
is conservative (paper, proof of Lemma 1.9).

*Theorem S. Let d ≥ 4 be even and S ⊆ Z/d ∖ {0}. If the bounded
subset-sum set*

    M(S) = { Σ_{v∈S} e_v·v  :  e_v ∈ {0, 1, 2} }

*is not all of Z/d, then |S| ≤ d/2 − 1.*

**Proof.** Write M = A₁ + ⋯ + A_k with A_i = {0, v_i, 2v_i}, k = |S|,
and let H = Stab(M) = {h : M + h = M}. Kneser's theorem gives

    |M| ≥ Σ_i |A_i + H| − (k − 1)|H|.

*Case H = {0}.* |A_i| = 3 for every v_i except v_i = d/2 (where
2v_i = 0 and |A_i| = 2), and at most one element of S equals d/2. So
|M| ≥ (3k − 1) − (k − 1) = 2k. Since M ≠ Z/d, 2k ≤ d − 1, and d even
forces k ≤ d/2 − 1.

*Case |H| = h > 1.* M is a union of H-cosets and M ≠ Z/d, so
|M| ≤ d − h. Split S: k₀ = |S ∩ H| ≤ h − 1 (distinct nonzero elements
of H) and k₁ = k − k₀. For v ∈ H, |A_v + H| = h; for v ∉ H,
A_v + H ⊇ H ∪ (v + H), so |A_v + H| ≥ 2h. Kneser gives

    d − h ≥ |M| ≥ h·(k₀ + 2k₁ − k + 1) = h·(k₁ + 1),

so k₁ ≤ d/h − 2 and k ≤ (h − 1) + (d/h − 2) = h + d/h − 3. For every
divisor h with 2 ≤ h ≤ d/2 the quadratic h² − (d/2 + 2)h + d ≤ 0 (roots
2 and d/2), i.e. h + d/h − 3 ≤ d/2 − 1. ∎

The bound is **tight**: S = the even classes (the character-type/all-QR
configurations) has |S| = d/2 − 1 and M(S) = the even subgroup.

**Corollary (Lemma S for every prime R ≡ 3 mod 4 — no upper limit).**
In discrete-log coordinates the divisor classes of m² contain exactly
such an M(S) (multiplicities ≥ 1 only enlarge the exponent budgets —
monotonicity), so if the nonzero factor-class support of (p+R)/4 has
size ≥ (R−1)/2, *every* class mod R is a divisor class of m² — in
particular −m — and residual R **succeeds**, for every class of p and
without invoking the p-powers. Failure therefore forces support
≤ (R−3)/2, i.e. the factors of (p+R)/4 lie in at most (R−1)/2 of the
R−1 unit classes: at least half the classes are forbidden, in finitely
many maximal-support branches, each a sifting condition of dimension
≥ ½. The twelve machine-verified instances 19 ≤ R ≤ 107 (below) are
special cases; "Lemma S past 107" is closed for **all** R at once.

**General abelian form (composite residuals).** The proof never used
cyclicity. In any finite abelian group G of even order g (multiplicative
notation, M(S) = ∏_{v∈S}{1, v, v²}): if M(S) ≠ G then

    |S| ≤ max( ⌊(g + t − 2)/2⌋ , h + g/h − 3 ) ≤ g/2   whenever t ≤ 3,

where t = #involutions of G (in the H-trivial case each involution in S
has |{1, v, v²}| = 2, losing one unit) and h ranges over proper subgroup
orders. For G = (Z/R)\* with ω(R) ≤ 2 distinct prime factors —
**every** composite admissible R ≤ 107 — t = 2^ω − 1 ≤ 3, so failure at
R forbids at least φ(R)/2 unit classes: **the composite residuals join
the chain on equal footing, dimension ≥ ½ each.** Caveat: Kneser alone
gives support ≤ g/2, i.e. only φ(R)/2 − 1 forbidden classes (dimension
½ − 1/φ(R)); the upgrade to support ≤ g/2 − 1 — the full φ(R)/2,
dimension ½ — is at present verified numerically only for the
composite R ≤ 107, via `theory.kneser_support_general`: the maximum
support of a
proper product-set is *exactly* g/2 − 1 for every composite admissible
R ≤ 107 (e.g. R = 15: g = 8, max 3; R = 91: g = 72, max 35; R = 95:
g = 72, max 35 — DP over 427 266 resp. 583 455 realizable product-sets).

**Independent machine confirmation (the former proof).** Reachability is
monotone in support and multiplicities, so checking all supports of size
(R−1)/2 at minimal multiplicities suffices; exhaustive check
(`theory.verify_support_bound`): 437 580 pairs at R = 19, 7 759 752 at
R = 23 — zero failures; and the strong (Kneser) form — every mask
realized by ≥ (R−1)/2 nonzero classes is full, `theory.verify_support_bound_strong` —
holds with the observed maximum non-full support exactly (R−3)/2 at
every prime residual checked. The check ignores the consistency relation
∏(classes) ≡ 4⁻¹p: it examines a superset of realizable configurations,
so it (and Theorem S) are conservative.

#### Theorem F ({3,7,11}; exponent 5/2)

*The number of hard primes p ≤ x failing residuals 3, 7 and 11
simultaneously (in particular, with R_min(p) > 11) is
O(x/(log x)^{5/2}); all but a proportion O((log x)^{−3/2}) of hard primes
are solved within {3, 7, 11}.*

**Proof.** With n = (p+3)/4, the three shifted forms are n, n+1, n+2. By
Theorems A, A′, and A″, joint failure implies: n free of primes
≡ 2 (mod 3); n+1 free of non-residues mod 7; and, splitting by A″'s two
cases: **branch (a)** — n+2 free of the five non-residue classes mod 11
(density ½); **branch (b)** — n+2 free of the six classes {4,5,7,8,9,10}
mod 11 (density 3/5). Each branch is a four-form sieve problem
(n, n+1, n+2, 4n−3) as in Theorem E, of dimension 1+½+½+½ = 5/2, resp.
1+½+½+3/5 = 13/5. The Fundamental Lemma bounds branch (a) by
O(x/(log x)^{5/2}) and branch (b) by O(x/(log x)^{13/5}) = o(the former).
Sum over the two branches and the six hard classes. ∎

#### Theorem G ({3,7,11,19}; exponent 3)

*The number of hard primes p ≤ x failing residuals 3, 7, 11 and 19
simultaneously (in particular, with R_min(p) > 19) is O(x/(log x)³);
all but O((log x)^{−2}) of hard primes are solved within {3, 7, 11, 19}.*

**Proof.** Add the form (p+19)/4 = n+4. By Lemma S at R = 19, failure at
19 splits into finitely many branches, each forbidding an explicit set of
≥ 9 of the 18 unit classes mod 19 on n+4 — dimension ≥ ½. Crossing with
the (a)/(b) branches at 11 gives finitely many combined branches, each a
five-form sieve problem (n, n+1, n+2, n+4, 4n−3) of dimension
≥ 1+½+½+½+½ = 3. (The forbidden residue classes of the five forms are
pairwise distinct for q > 19; smaller primes are absorbed into the fixed
congruence class of n.) The Fundamental Lemma bounds each branch by
O(x/(log x)³); sum over the finitely many branches. ∎

#### Theorem G′ ({3,7,11,19,23}; exponent 7/2)

*Identically, with Lemma S at R = 23 and the form (p+23)/4 = n+5:
the joint exceptional set of {3, 7, 11, 19, 23} is O(x/(log x)^{7/2}).*

**The chain — no longer capped at R = 107.** Every residual with a
support bound adds ½ to the exponent, and Theorem S now supplies the
bound for every admissible R at once — the chain extends to arbitrary
finite residual lists, primes and composites alike. Historically the
bound was verified one residual at a time: naive cost is
C(R−2, (R−1)/2) reachability checks, which explodes past R = 31; the
**subset dynamic program** (`theory.verify_support_bound_dp`) folds all
supports into a table mapping each reachability mask to the maximal
support size achieving it (valid because failure at any multiplicities
implies failure at multiplicity 1, by monotonicity). Realized masks are
heavily structured, so the state count stays tractable — these runs now
stand as independent confirmations of Theorem S:

| R | states | time | violations |
|---:|---:|---:|---:|
| 19 | 271 | <0.1 s | 0 |
| 23 | 790 | <0.1 s | 0 |
| 31 | 3 001 | <0.1 s | 0 |
| 43 | 20 559 | 0.1 s | 0 |
| 47 | 40 573 | 0.2 s | 0 |
| 59 | 203 978 | 1.7 s | 0 |
| 67 | 470 070 | 4.2 s | 0 |
| 71 | 764 895 | 7.2 s | 0 |
| 79 | 1 529 223 | 16 s | 0 |
| 83 | 2 414 145 | 28 s | 0 |
| 103 | 12 998 639 | 220 s | 0 |
| 107 | 19 530 971 | 331 s | 0 |

**Theorem H (the chain, upgraded by Theorem S).** *(i) For every finite
set P of admissible residuals R ≡ 3 (mod 4) — prime or composite (with
ω(R) ≤ 2 for the composites) — the number of hard primes p ≤ x failing
every residual in P is O_P(x/(log x)^{1+|P|/2}). (ii) In particular,
for P = all fifteen primes ≡ 3 (mod 4) up to 107 the exponent is 17/2,
and for the full 27-residual admissible list ≤ 107 (primes and
composites) it is 29/2.*

Proof: identical to Theorem G — the forms (p+R)/4 = n + (R−3)/4 are
distinct integer shifts of n; Theorems A/A′/A″/A‴ handle 3, 7, 11, 15
and Theorem S handles every other residual (prime via the corollary,
composite via the general abelian form); each contributes dimension ≥ ½
through finitely many maximal-support branches, plus 1 for primality:
total ≥ 1 + |P|/2. The Fundamental Lemma applies to each of the
finitely many combined branches (the forbidden residue classes of the
distinct forms are pairwise distinct for q > max P; smaller primes are
absorbed into the fixed congruence class of n). ∎

The exponent is now bounded only by the *number of residuals used* —
the constants O_P blow up with |P| (branch counts and the
(log x)^{#forms} remainder of the Fundamental Lemma), which is exactly
the growing-list wall of §2.8, Attempt 2.

#### Theorem I (aggregate identity families) and the 19/2 upgrade

*Let p ≡ 1 (mod 4) be prime and R ≡ 3 (mod 4). If R | p+1, then k = a·p²
is a certificate for residual R; if R | p+4, then k = a²·p is. Hence any
prime factor ≡ 3 (mod 4) of either p+1 or p+4 yields an explicit
solution.*

**Proof.** k = a p² divides m² = p²a² and k ≡ −m ⟺ ap² ≡ −pa ⟺ p ≡ −1
(mod R); k = a²p divides m² and a²p ≡ −pa ⟺ a ≡ −1 ⟺ 4⁻¹p ≡ −1 ⟺
p ≡ −4 (mod R). Integrality of b, c is automatic as always. ∎

These are *aggregate* conditions — one multiplicative condition on p+1
(resp. p+4) simultaneously activates every residual dividing it. A scan
of the a-independent divisor shapes k = a^j p^i shows these two are the
**only** such families. Verified on the 10⁹ data: the two families alone
cover **74.2 %** of hard primes (random sample of 3 000), and none of the
four critical primes — whose p+1 and p+4 must accordingly be free of
3-mod-4 prime factors, a strong structural characterization of them.

**Sieve consequence.** Failure of both families means (p+1)/2 and p+4
(two new primitive linear forms, 2n−1 and 4n+1 in n = (p+3)/4) are free
of primes ≡ 3 (mod 4): two further sifting conditions of dimension ½
each. (The certifying shapes k = a^j p^i are the only a-independent
ones with j, i ≤ 2.) Added
to Theorem H: *the number of hard primes p ≤ x failing all fifteen prime
residuals up to 107 **and** both aggregate families is
O(x/(log x)^{19/2}); with the full 27-residual admissible list ≤ 107
(Theorem S general form) the exponent is **31/2**.*

**Context (known bounds).** For calibration: Vaughan's classical
mean-value bound gives an exceptional set ≪ x·exp(−c(log x)^{2/3}) for
the Erdős–Straus equation — asymptotically stronger than any fixed power
of log x. The value of the present chain is not raw density but its
explicit, certificate-generating, machine-verified structure.

**Limit of the method (important).** No fixed finite list can be pushed
to *emptiness* this way: a constant-dimension sieve bounds counts by
x/(log x)^κ, which diverges for every fixed κ. Moreover the calibrated
independence model predicts the joint-failure density of ANY fixed list
is a positive constant times (log x)^{−κ(S)} — i.e. infinitely many
exceptional primes are expected for every fixed S, with the record
minimal residual growing slowly (roughly logarithmically) without bound.
The finite covering hypothesis in its fixed-list form is therefore
probably **false**; the correctly-posed target is a slowly growing bound
R_min(p) ≪ f(p), which requires existence (lower-bound) technology
beyond upper-bound sieves.

### 2.8 Two attempts at totality, and their walls

Both attempts below were executed; each yields something real, and each
hits a wall that is now *precisely characterized* rather than merely
suspected.

#### Attempt 1 (constructive): aggregate families

Outcome: Theorem I above — the complete list of a-independent divisor
identities is {p+1, p+4}; they cover 74 % of hard primes and add +1 to
the chain exponent. Wall: any family of this shape covers p through a
multiplicative condition on a *single shifted value*, so its failure set
has density ~(log x)^{−1/2} — positive at every finite level. The four
critical primes already escape both families. Constructive families
thicken the almost-all coverage but structurally cannot reach totality.

#### Attempt 2 (analytic): growing lists and the larger sieve

Idea: let the residual list grow with p (B ≈ C log p), so the sieve
dimension grows and the count bound x/(log x)^{κ(B)} could in principle
drop below 1 — proving R_min(p) ≤ C log p outright. (Note: by the
completeness remark below, *any* unconditional bound R_min(p) ≤ f(p) is
equivalent in strength to the conjecture at p itself; this attempt is
recorded to characterize the wall, not as an intermediate milestone.)
Two requirements emerge:

1. **p-independent forbidden classes.** The per-branch half-density
   forbidden sets of Lemma S depend on p mod R; aggregating them over
   ~log x residuals requires conditioning on p mod ∏R ≈ e^{B/2} ≈ x² —
   more classes than there are primes ≤ x. Only *p-independent* (branch-
   and p-class-free) forbidden classes can be aggregated. Computing this
   set exhaustively (forced-class DP over all configurations and all p
   classes, R = 11 … 43; an exploratory computation whose driver is not
   among the repo's named entry points): **the always-forbidden set is
   exactly one class — the universal class −4⁻¹ (mod R) — at every R
   tested.** Every
   other class occurs in some failing configuration. So the aggregable
   sifting weight per modulus q is W(q) = #{R ≤ B : R | 4q+1}, of average
   ~½ log B — not the ~B/log B that half-density sets would give.

2. **The support-level cap.** Even granting stronger inputs, the larger
   sieve's quantity L is capped by the constraint d ≤ Q: moduli usable
   for the growing list have size ≥ B, so at most log Q/log B ≈
   log x/(2 log log x) of them fit into one squarefree d, giving
   L ≤ exp(O(log x/log log x)) — never ≥ x. The same cap appears as the
   remainder-term explosion (log x)^{#forms} in the fundamental lemma.

Outcome (heuristic ceiling, not a claimed theorem — the paper asserts
nothing of this shape): the growing-list route would yield at best a
bound of shape x·exp(−c(log log x)²) — beyond every fixed power of log,
but (a) still divergent, and (b) weaker than Vaughan's classical
x·exp(−c(log x)^{2/3}). The wall is not technical laziness: it is the
collapse of the p-independent forbidden structure to a single class,
measured exactly by the AF computation.

### 2.9 The reciprocity structure theorem: joint failure explained

The open problem "explain the record prime" is now substantially
resolved by a clean structural identity.

#### Theorem J (reciprocity structure)

*Let p be a hard prime, R ≡ 3 (mod 4) prime, and q an odd prime factor
of a_R = (p+R)/4 (necessarily q ≠ R). Then*

    (q | R) = (p | q).

**Proof.** q | p+R gives R ≡ −p (mod q). By quadratic reciprocity with
R ≡ 3 (mod 4): (q|R) = (−1)^{(q−1)/2}(R|q) =
(−1)^{(q−1)/2}(−1|q)(p|q) = (−1)^{(q−1)/2}·(−1)^{(q−1)/2}·(p|q) =
(p|q). ∎

**Corollary J1 (forced primes are character-neutral).** The hard classes
are the squares mod 840, so p is automatically a QR mod 3, 5, and 7, and
p ≡ 1 (mod 8) handles q = 2 (2 | a_R only for R ≡ 7 mod 8, where
(2|R) = +1). Hence the small primes forced into the shifted values by
the Mordell structure can never break a character failure — a conceptual
explanation of *why* the hard classes are exactly the square classes.
Verified: 61 438 forced-prime instances in the data, zero violations
(and 135 588 instances of Theorem J itself, zero violations).

**Corollary J2 (joint character-type criterion).** p fails character-type at every prime
residual R ≤ B simultaneously ⟺ (p|R) = +1 for each such R and
**(p|q) = +1 for every unforced odd prime q dividing any of the shifted
values (p+R)/4, R ≤ B.** One condition per *distinct* prime q, shared
across every residual q divides.

#### The record prime, described quantitatively

Corollary J2 identifies the correct "coins": joint failure requires a
positive fluctuation in the independent-looking signs (p|q) over the
distinct primes q of the interval, plus budget-type luck where signs come up
−1. Smooth shifted values reduce the number of distinct primes — fewer
coins to win. Measured for the record p = 8 803 369 against typical
hard primes of its size:

| | distinct odd primes over 27 shifted values | share with (p\|q)=+1 |
|---|---:|---:|
| record 8 803 369 | **43** | **81 %** |
| typical (5 samples) | 45–52 | 44–60 % |

An extreme value of provably-the-right statistic. **No significance
level is attached to it** (an earlier draft claimed "≈4σ"; that was a
look-elsewhere artifact — the prime was selected *because* it was the
record, so an extreme order statistic in a correlated quantity is
expected, not surprising). The statement the table supports is
descriptive: it says what a record prime looks like mechanically. The
record is then a statement about large deviations of Legendre-symbol
coin flips over interval factorizations: rarer at larger p only because
the number of coins D(B, p) grows like (B/4)·log log p, giving the
growth law **B(x) ≍ log x / log log x** for the pure-character-type
record (the observed mixed character-type/budget-type record sits above
this, budget-type escapes absorbing a few −1 coins — 8 803 369's 8
negative coins are exactly its 14 budget-type failures' worth of luck).
The record
was static from 10⁷ to 10¹¹ and moved to R = 111 at 10¹² (§5, §6),
which is the qualitative behaviour this growth law calls for: motion,
but glacially slow in log x.

#### Theorem K (conditional falsity of the finite covering hypothesis)

*Assume Dickson's conjecture (prime k-tuples). Then for every B there
are infinitely many hard primes p with R_min(p) > B.*

**Construction sketch.** Fix the interval pattern: choose n mod a smooth
modulus so each a_R = (p+R)/4 (R ≤ B admissible) has exactly its forced
smooth part s_R (character-neutral by Corollary J1) times a cofactor
c_R. The system {c_R = (n + (R−3)/4)/s_R} ∪ {4n−3} is an admissible
family of linear forms; impose on each prospective prime c_R the
congruence conditions "c_R ≡ QR class (mod r)" for every prime
r ≤ B, r ≡ 3 (mod 4) (finitely many congruences, compatible by CRT),
and on p = 4n−3 the hard-class congruence. Dickson's conjecture supplies
infinitely many n making all forms prime; then every prime factor of
every a_R is a QR mod every relevant r — Proposition 1 forces failure at
every R ≤ B. ∎ (sketch)

Consequently, **under standard conjectures the fixed-list covering
hypothesis is false and the record grows without bound** — matching the
calibrated model. Unconditional falsity appears out of reach: already
"infinitely many hard p fail R = 3" contains a two-form prime-tuple
statement (a₃ and 4a₃−3 simultaneously prime in classes), i.e. is
twin-prime-hard.

#### Verdict

Upper-bound counting — fixed lists, growing lists, aggregate families,
in any combination available to us — bounds the exceptional set but
cannot empty it. The residual method's genuine frontier is an existence
statement (some R ≤ f(p) works for *every* p), which no upper-bound
sieve can deliver. Candidate genuinely-new inputs, in increasing order
of speculation: (i) additive-combinatorial theorems (Olson-type bounded
subset sums in cyclic groups) proving failing supports at every R are
either small or subgroup-trapped — **now done at the fixed-R level:
Theorem S (§2.7) proves via Kneser's theorem that failing supports are
small (≤ (R−3)/2), and its proof shows the extremal ones are
subgroup-trapped (the stabilizer H is nontrivial and S concentrates on
H up to ≤ d/h − 2 outliers)**. What the fixed-R statement does *not* by
itself deliver is the growing-list aggregation: the per-branch forbidden
classes remain p-dependent and the branch count per residual, though
finite, grows — walls 1 and 2 of §2.8 stand. Passing Vaughan would
require the subgroup-trapped structure to be exploited *uniformly in R*
(fewer, p-independent branches), which is now a well-posed additive-
combinatorics question rather than a computation; (ii)
bilinear/dispersion estimates treating p and the factors of p+R
symmetrically; (iii) a mean-value treatment of the certificate count
itself (the Vaughan route) upgraded with the residual structure.

### 2.10 The Burgess/reciprocity route: Jacobi necessity, purity, and the selected-residual census

Theorem S closed the fixed-list axis; this section records the route
that opened in its place, together with the Step-1 census that tests it
(entry point: `erdos_straus.burgess_scan`; archive:
`data/analysis/burgess_scan_1e9.json`).

#### Lemma J° (composite reciprocity)

*Let R ≡ 3 (mod 4) be any admissible residual (prime or composite), and
q an odd prime with q | (p+R)/4 and gcd(q, R) = 1. Then the Jacobi
symbol satisfies (q|R) = (p|q).*

**Proof.** q | p + R gives R ≡ −p (mod q). Jacobi reciprocity with
R ≡ 3 (mod 4): (q|R) = (−1)^((q−1)/2) (R|q) =
(−1)^((q−1)/2) (−1|q)(p|q) = (p|q). ∎ (For prime R this is Theorem J;
the proof never used primality. Verified mechanically at every selected
residual over all 1,587,581 hard primes below 10⁹ — zero violations —
and as a permanent test in the suite.)

#### Lemma N (Jacobi necessity — the dichotomy's easy half, all R)

*For every admissible R: if no prime factor of a = (p+R)/4 has Jacobi
symbol (q|R) = −1, then residual R fails at p.*

**Proof.** All factors of a Jacobi-QR ⟹ (a|R) = +1; consistency
a ≡ 4⁻¹p (mod R) gives (p|R) = (4a|R) = (a|R) = +1 — so *every* prime
factor of m = pa has symbol +1, hence every divisor k of m² has
(k|R) = +1, while the target has (−m|R) = (−1|R) = −1 for R ≡ 3
(mod 4). ∎

Empirically the converse direction never failed in the other sense
either: across all 27 residuals × ~80,000 sampled primes, **zero**
successes occurred without a Jacobi non-residue factor — Lemma N is
sharp in the data. Call R **C1-pure** (at hard primes) when the
converse implication also holds: a Jacobi non-residue factor present ⟹
success. Pure residuals are proved for R = 3, 7, 15 (Theorems A, A′,
A‴).

#### Purity census (10⁹ masks, every 20th prime)

Only the three proven residuals are pure; everywhere else the
"budget-in-the-wild" rate (fraction of primes with a non-residue factor
at which R still fails) is:

| R | rate | R | rate | R | rate |
|---:|---:|---:|---:|---:|---:|
| 3 | **0** | 39 | 6.9 % | 75 | 47.1 % |
| 7 | **0** | 43 | 63.8 % | 79 | 29.6 % |
| 11 | 4.3 % | 47 | 4.9 % | 83 | 40.3 % |
| 15 | **0** | 51 | 47.2 % | 87 | 26.4 % |
| 19 | 21.7 % | 55 | 18.5 % | 91 | 66.4 % |
| 23 | 1.3 % | 59 | 19.8 % | 95 | 12.6 % |
| 27 | 22.6 % | 63 | 14.5 % | 99 | 66.2 % |
| 31 | 8.7 % | 67 | 73.0 % | 103 | 38.6 % |
| 35 | 11.9 % | 71 | 7.5 % | 107 | 57.0 % |

So the naive hypothesis "a pure residual exists in every needed
progression" is false — purity is rare and (per the generic
configuration scan) it is a *hard-prime* phenomenon: even R = 7 has
budget-failure states before the forced factor 2 kills them.

#### The selected-residual census (all 1,587,581 hard primes < 10⁹)

For each hard prime take the **least Legendre non-residue** q (hard
primes are QRs mod 3, 5, 7, so q ≥ 11; observed range 11…83, GRH-scale
(log p)²) and the **selected residual** R = (−p) mod 4q — the least
R ≡ 3 (mod 4) with q | (p+R)/4. By Lemma J°, (q|R) = (p|q) = −1, so
the all-Jacobi-QR failure mode of Lemma N is impossible at R. Results:

- **Single shot: 94.78 %** of hard primes succeed at the selected R
  (1,504,773 / 1,587,581).
- **Failure anatomy:** of 82,808 failures, 82,401 are budget failures
  and only 407 are per-prime character obstructions at composite R
  (all factors QR mod some prime r | R despite the Jacobi non-residue)
  — the construction almost never strands a prime on characters.
- **The q-ladder** (retry R + 4q, R + 8q, … ≤ 400, same q): resolves
  86 % of failures on the second rung, 99.98 % of all primes within
  the histogram 2:71,350 / 3:7,595 / 4:1,801 / 5:670 / 6–9:97;
  1,295 primes exhaust the first-q ladder below 400.
- **The second-q ladder:** every one of those 1,295 resolves with a
  later non-residue q (same construction, R ≤ 400). **Coverage below
  10⁹ is 100.0 % with R ≤ 400** across at most two q's.

#### Scaling to 10¹⁰ and 10¹¹ (window samples + the complete deep tail)

Above 10⁹ there are no full masks, so success at each rung is computed
directly with the composite exact engine (archive:
`data/analysis/burgess_scan_1e10_1e11.json`; the engine agrees with the
stored R_min on a systematic tail sample, 0/101 disagreements).
Systematic window samples of 10,000 hard primes per half-decade:

| range | first-shot | ladder ≤ 400 |
|---|---:|---:|
| 10⁹–3.2×10⁹ | 95.4 % | **100 %** |
| 3.2×10⁹–10¹⁰ | 95.0 % | **100 %** |
| 10¹⁰–3.2×10¹⁰ | 95.8 % | **100 %** |
| 3.2×10¹⁰–10¹¹ | 95.7 % | **100 %** |

**No drift**: the first-shot rate is flat (slightly rising) across two
decades, and the ladder resolved every one of the 40,000 sampled primes.
The adversarial population — the complete 10¹¹ deep tail, all 20,151
primes with R_min ≥ 43, which by construction fail every small residual
— still gives first-shot 75.1 % and ladder 99.990 %: exactly two primes
(23,248,669,921 and 55,952,434,561, both with unusually large least
non-residues q₁ = 67, 83) exhaust the 400-cap, and both resolve at
R = 407 resp. 435 — so tail coverage is also 100 % at cap 435. The
budget-failure probability per rung shows no growth with p, which is
what Hypothesis B needs.

#### Anatomy of budget failures (archive: `burgess_failures_1e9.json`)

Full reach diagnostics for all 82,808 selected-residual failures below
10⁹, against a 79,150-prime success control (entry point:
`burgess_scan.characterize_budget_failures`):

- **97.5 % are true budget failures**: the subgroup generated by the
  present factor classes (with the structural p-powers) *contains* the
  target — only the bounded exponents miss it. Just 2.5 % are subgroup
  misses (target outside the generated subgroup; no budget cures
  those), and 29.1 % of all failures miss *exactly one* unit class:
  the target itself.
- **Failing supports are tiny — an observed hard cutoff.** No failure
  has more than 5 distinct non-identity factor classes (Theorem S
  allows up to (R−3)/2 ≈ 12–50 at these residuals). The conditional
  failure probability by support size s is a steep geometric law:

  | s | 1 | 2 | 3 | 4 | 5 | ≥ 6 |
  |---|---:|---:|---:|---:|---:|---:|
  | P(fail \| s) | 3.0 % | 27.4 % | 8.0 % | 1.2 % | 0.08 % | 0 (0 / 59,774) |

  Roughly a factor ~7 per additional class beyond s = 2. A rung fails
  essentially only when a = (p+R)/4 is atypically class-concentrated;
  since ω(a) has Erdős–Kac statistics, this is the quantitative
  mechanism behind the flat ≈ 5 % per-rung failure rate.
- **The non-residue part sits at its parity minimum.** By consistency,
  (a|R) = (p|R), so Jacobi non-residue factors occur with total
  multiplicity of fixed parity; in 97.9 % of failures that
  multiplicity is exactly the minimum allowed (1 when (p|R) = −1,
  else 2) — the R = 15 proof mechanism, observed at every residual.

Proof target for Hypothesis L, sharpened: bound the probability that
a = (p+R)/4 simultaneously (i) has ≤ 5 non-identity classes mod R,
(ii) carries minimal non-residue mass, and (iii) its bounded-exponent
reach misses one specific class — along a ladder whose rungs refresh
a by +q each step. Each ingredient is a classical-flavored statement
about prime factors of shifted integers in residue classes.

#### Theorem L₀ (rigorous ladder chain, fixed length)

*Let q ≥ 11 be prime and J ≥ 1 fixed. For a hard prime p with
(p|q) = −1 let R₀ = (−p) mod 4q and R_j = R₀ + 4qj. Then the number
of hard primes p ≤ x with (p|q) = −1 that fail every rung R_j,
0 ≤ j < J is*

    O_{q,J}( x / (log x)^{1 + J'/2} ),

*where J' = #{j < J : ω(R_j) ≤ 2} is the number of usable rungs
(J' = J for every ladder observed below 10⁹; rungs with three or more
prime factors — the smallest admissible case, R ≡ 3 (mod 4) with
ω(R) ≥ 3, is R = 195 = 3·5·13 — are skipped).*

**Proof sketch.** The rungs are admissible (R_j ≡ 3 mod 4 since
p ≡ 1 mod 4), and the shifted forms a_j = (p+R_j)/4 = n + (R₀−3)/4 + qj
(n = (p+3)/4) are distinct integer linear forms in n with pairwise
distinct shifts. By Theorem S — part (ii) for prime rungs, part (iii)
for composite rungs with ω ≤ 2 — failure at rung R_j forbids at least
half the unit classes mod R_j for the prime factors of a_j, through
finitely many maximal-support branches: a sifting condition of
dimension ≥ 1/2 per rung, exactly as in the chain (Theorem 1.11),
whose proof applies verbatim to the list {R_j} with constants
depending on q and J. Dropping the character condition (p|q) = −1
only enlarges the sifted set, so the upper bound survives it. ∎

Theorem L₀ is the ladder-adapted chain: unlike the fixed-list chain it
bounds failures of a **p-adapted** residual family, so it composes
with the distribution of the least non-residue. Two remarks. (i) Rungs
with ω(R_j) ≥ 3 (the smallest admissible such rung is
R = 195 = 3·5·13) are simply skipped —
Theorem S(iii) currently covers ω ≤ 2; and composite rungs beyond 107
carry only the unconditional Kneser tier of S(iii) — dimension
½ − 1/φ(R_j) instead of ½ — which changes no divergence or
summability conclusion. (ii) For fixed J this adds no
density strength over Theorem 1.11; its role is structural, as the
rigorous base of the conditional theorem below.

#### Theorem B₁ (the first rung of B, proved)

*Fix a prime q ≥ 11 and δ ∈ (0, 1). For x ≥ x₀(q, δ), among the hard
primes p ≤ x with least non-residue q(p) = q, the proportion of hard
primes failing their selected residual R₀ = (−p) mod 4q is*

    ≪_q  (log x)^{−1/φ(R₀)}  →  0

*per class fixing R₀; over all classes the proportion is governed by
the worst class, i.e. by min 1/φ(R₀) over the admissible R₀ < 4q that
occur. So Hypothesis B's inequality holds at j = 0, for every fixed
q, with any δ < 1 eventually.*

**Proof.** The condition q(p) = q is a conjunction of quadratic-residue
conditions at the primes 11, …, q, i.e. a union U of reduced residue
classes mod M = 840·∏_{11 ≤ ℓ ≤ q} ℓ; fix one class c ∈ U (mod
lcm(M, 4q)), which fixes R₀ = R(c) and forces q | (p+R₀)/4. By
Dirichlet/Siegel–Walfisz, primes in the class number
∼ x/(φ(M')·log x) — a positive proportion of E₀ per class (notation
defined below with Hypothesis B), finitely many classes.

Key step (Proposition 2.2, universal class): if n = (p+R₀)/4 has any
prime factor u ≡ −4⁻¹ (mod R₀), then k = u·p² is a certificate and
rung R₀ succeeds. Hence a failing p in the class has
n ≡ n_c (mod M''), 4n − R₀ = p prime, and **n free of prime factors
≡ −4⁻¹ (mod R₀)**. Sift {n ≤ (x+R₀)/4 : n ≡ n_c (mod M'')} by the
primes ℓ ≤ z = x^{1/10}, ℓ ∤ M'': forbidden classes are
4n ≡ R₀ (mod ℓ) always (primality of p, one class), plus
n ≡ 0 (mod ℓ) when ℓ ≡ −4⁻¹ (mod R₀) (one further class, distinct
from the first for every ℓ ∤ R₀). By Dirichlet the sifting dimension
is κ = 1 + 1/φ(R₀), and the Fundamental Lemma gives

    #(failing p in the class) ≪ x / (log x)^{1 + 1/φ(R₀)}.

Dividing by the class's ∼ x/(φ(M')·log x) primes and summing the
finitely many classes: the failing fraction is
≪_q (log x)^{−1/φ(R₀)} → 0 per class, hence over all classes
≪_q (log x)^{−min 1/φ(R₀)} (minimum over the admissible R₀ < 4q
that occur). ∎

**Corollary (uniform range).** Since M = e^{O(q)} ≤ (log x)^{O(1)} for
q ≤ c₀ log log x, Siegel–Walfisz and the Fundamental Lemma apply
uniformly there, and the failing fraction is
≤ exp(−c₁ log log x / q) ≤ 1 − δ₀ for q ≤ c₂ log log x: **B's first
rung holds with a uniform δ₀ for all q up to c log log x** (which by
Lemma Q, stated below, covers all hard primes outside a set of
relative density 2^{−π(c log log x)}). The x₀ is ineffective
(Siegel–Walfisz).

**Data checks.** (i) The proof's mechanism is exact in the census:
across 11,816 sampled selected-rung failures below 10⁹, *none* has a
prime factor of (p+R₀)/4 in any of the Prop 2.2 classes
{t, tp⁻¹, tp⁻²} — zero violations, as the contrapositive requires.
(ii) A bonus channel the proof doesn't even need: for 25.5 % of hard
primes the selected q itself lies in the universal class
(4q ≡ −1 mod R₀), so the closed-form certificate k = q(p)·p² solves p
at R₀ outright — a p-adapted identity family in the sense of
Prop. 1.12.

**What remains for j ≥ 1.** Applying the same sieve to rung j alone
bounds each unconditional failing set (that is Theorem L₀). The open
content of B is the *conditional* inequality — that rung j+1 removes
a δ-fraction *of the survivors of rungs 0…j*, whose set is already
sieve-thin; the rung map a ↦ a + q refreshes the factorization, and
making that refresh rigorous against a conditioned set is precisely
the remaining gap between B₁ and B.

#### Hypothesis B and Theorem L₁ (the almost-all draft)

The census makes the following counting hypothesis precise and
falsifiable. For x, a prime q, and j ≥ 0 let E_j(x) be the set of
hard primes p ≤ x with (p|q(p)) = −1, q(p) = q its least non-residue,
that fail rungs R₀, …, R_j of their q-ladder.

**Hypothesis B(δ, J(x)).** There are δ > 0 and x₀ such that for all
x ≥ x₀, all q ≤ (log x)², and all 0 ≤ j < J(x):

    #E_{j+1}(x)  ≤  (1 − δ) · #E_j(x)  +  O(√x).

*Status*: the j = 0 case is **proved** (Theorem B₁ above), for every
fixed q and uniformly for q ≪ log log x. *Measured*: the census gives
per-rung survival factors 1 − δ ≈
0.05–0.14 at every scale tested (10⁹ exhaustively; 10¹⁰–10¹¹ sampled;
the 10¹¹ deep tail completely), with no drift in p, through ~9 rungs
and two q's. The anatomy subsection above is the proof target: a rung
survives only via the triple coincidence (class-concentration ≤ 5,
parity-minimal non-residue mass, one-class reach deficiency), and the
rung map a ↦ a + q refreshes the factorization.

**Lemma Q (least non-residue, large sieve).** The number of hard
primes p ≤ x whose least non-residue exceeds y is
≪ x · 2^{−(π(y) − 4)} for y ≤ exp(c√(log x)) (large sieve /
Linnik-style: such p are quadratic residues modulo every prime in
(7, y], a half-class condition per modulus; hard primes already
satisfy it for 3, 5, 7). In particular the primes with
q(p) > (log x)² number ≪ x·exp(−c(log x)²/log log x). (Observed:
q ≤ 83 below 10¹¹; GRH puts q(p) ≪ (log p)² for every p.)

**Theorem L₁ (conditional on B).** *Assume Hypothesis B(δ, J(x)).
Then all but*

    O( x · e^{−δ J(x)}  +  x · 2^{−π((log x)²)} )

*hard primes p ≤ x satisfy R_min(p) ≤ 4 q(p) (J(x)+1) ≤
(log x)^{2+o(1)} J(x). The second error term is
exp(−c(log x)²/log log x)·x — negligible against the first at every
calibration.*

**Proof.** Lemma Q disposes of primes with q(p) > (log x)²
(the second error term, which is ≪ x^{−A} for every A — negligible).
For the rest, iterate B: after J(x) rungs the surviving count is
≤ (1−δ)^{J(x)} x + O(J(x)√x). A survivor is the only way to have
R_min > 4q(J+1) along the ladder; everything else has a certificate
at some rung. ∎

**Calibrations.** With J(x) = (log log x)² (a mild extrapolation of
the measured 9 rungs): exceptional set ≪ x·exp(−δ(log log x)²) — past
every fixed power of log x, i.e. past the entire chain and Theorem
1.13, with the explicit residual bound R_min ≤ (log x)^{2+o(1)}. With
J(x) = (log x)^θ, θ > 2/3 (a bold extrapolation): exceptional set
≪ x·exp(−δ(log x)^θ) — past Vaughan. The hypothesis-strength needed
scales exactly with the ambition, and every increment is testable
before it is assumed.

**What would remain.** Theorem L₁, under any calibration, is an
almost-all statement: the emptiness wall (Remark 4.3 of the paper)
is untouched, and a single conspiratorial prime — a super-record
dodging J(x) rungs — is exactly what Hypothesis B cannot exclude
per-p and what Dickson-type constructions suggest exists for fixed
finite ladders. The full conjecture on this route = B plus the
per-p statement "no prime dodges its first J(p) rungs", which is a
simultaneous-multiplicative-structure assertion of prime-tuple
difficulty. The honest reading: the route upgrades the program's
frontier from fixed lists to p-adapted polylog ladders and localizes
the conjecture's difficulty into one measured, falsifiable counting
inequality — it does not remove that difficulty.

#### Theorem B₂ (the proxy ladder, two-sided) and the reduction of B to Hypothesis P

The obstruction to repeating B₁ at rung 1 is that Hypothesis B's
inequality is *conditional*: it needs the survivor set E_j bounded
below, and true failures are not sieve-defined. The resolution is to
run the ladder on the sieve-defined **avoidance proxy**

    Ẽ_j  =  { p ≡ c :  a_i = (p+R_i)/4 has no prime factor
                        ≡ −4⁻¹ (mod R_i),  for all i ≤ j },

so that E_j ⊆ Ẽ_j at every rung (Prop 2.2; exact in the data, zero
violations).

**Theorem B₂.** *Fix a prime q, a class c (fixing R₀, R₁, …), and
J with κ = Σ_{j<J} 1/φ(R_j) below an absolute constant. Then*

    x/(log x)^{1+κ}  ≪_{q,J}  #Ẽ_J(x)  ≪_{q,J}  x/(log x)^{1+κ},

*and consequently the proxy ladder decays exactly as B prescribes:
#Ẽ_{j+1}(x) ≍ (log x)^{−1/φ(R_{j+1})} · #Ẽ_j(x) for each j < J.*

**Proof sketch.** Upper bound: the Fundamental Lemma in dimension
1 + κ, as in B₁/L₀ — the forms a_i = n + q·i are distinct shifts, and
the forbidden classes n ≡ −qi (mod ℓ) for ℓ ≡ −4⁻¹ (mod R_i) are
pairwise distinct for ℓ ∤ q(i−i′). Lower bound (the new half): a
beta-sieve lower bound in dimension κ < 1 on the prime-supported
sequence {(p+R₀)/4 : p ≡ c prime}, with level x^{1/2−ε} from
Bombieri–Vinogradov, gives ≫ x/(log x)^{1+κ} integers avoiding the
forbidden classes at primes ℓ ≤ z = x^{1/10}; primes n with a
forbidden prime factor u > z are then removed by a
Brun–Titchmarsh/Fundamental-Lemma upper bound in the progressions
mod 4uM, whose total is ≪ (J log 5/min_j φ(R_j)) times the main
term — absorbable when κ is small, which is the stated constraint. ∎

**Hypothesis P (proportionality).** There is c_P > 0 with
#E_j(x) ≥ c_P · #Ẽ_j(x) for j ≤ J and x large: true failures are a
positive proportion of their necessary-condition set.

**Corollary B₃ (second rung and beyond, conditional on P).** Under P,
for every fixed j < J:

    #E_{j+1}(x)  ≤  #Ẽ_{j+1}(x)  ≪  (log x)^{−1/φ(R_{j+1})} · #Ẽ_j(x)
                 ≤  (log x)^{−1/φ(R_{j+1})} · c_P^{−1} · #E_j(x),

*so B's inequality holds at every fixed rung with any δ < 1 for
x ≥ x₀(q, j, δ). In particular the second rung of B follows from P
alone; nothing else is missing.*

**P measured** (10⁹ masks, every 20th prime; archive
`burgess_proxy_1e9.json`): the avoidance set contains 43.8 % of primes
at rung 0 and true failures are **12.0 %** of it; conditioned on a
true rung-0 failure, rung-1 failures are **15.9 %** of rung-1
avoiders. Proxy decay per rung 84.6 % (heading to the theorem's
(log x)^{−κ} asymptotically), true decay 13.5 %. Zero sanity
violations (E ⊆ Ẽ exact).

**P at scale** (mask-free, half-decade window samples of 10,000
primes each; archive `burgess_proxy_scaled.json`):

| range | avoid₀ | P₀ = fail/avoid | proxy decay | P₁ (within fail₀) |
|---|---:|---:|---:|---:|
| 10⁹–3.2×10⁹ | 43.1 % | 10.8 % | 83.4 % | 13.2 % |
| 3.2×10⁹–10¹⁰ | 42.9 % | 11.6 % | 84.2 % | 16.2 % |
| 10¹⁰–3.2×10¹⁰ | 43.3 % | 9.7 % | 84.1 % | 14.5 % |
| 3.2×10¹⁰–10¹¹ | 43.1 % | 9.9 % | 84.5 % | 14.8 % |

Every quantity Hypothesis P needs bounded is flat across two decades:
c_P sits at 9.7–12 % (rung 0) and 13–16 % (rung 1) with no sign of
vanishing, the avoidance density is constant at 43 %, and the proxy
decay matches the 10⁹ mask measurement. P's empirical standing now
equals B's before it: measured at every accessible scale, drift-free.

**The wall, isolated.** P is a *lower* bound on budget failures inside
a sieve-thin set — conditional on universal-class avoidance, the
class-concentration event of the anatomy must retain positive
probability. Lower-bounding a multiplicatively-defined thin event is
parity-flavored, and this is now the program's single unproved
ingredient: L₀ ✓, B₁ ✓, B₂ ✓, B ⟸ P, L₁ ⟸ B. Everything above P is
proved; everything below P is measured.

#### The norm-form bridge, the sharp first link (Theorem 5.7), and the ladder failure lower bound (Theorem 5.8, formerly "Theorem P₁")

> **Correction (August 2026, PR #56).** The statement previously printed
> here and in the paper as *Theorem P₁ (half-dimensional failure lower
> bound)* was **false as stated**, and the passage below replaces it.
> The old admissibility test asked only that R₀ have a prime factor
> r₁ ≡ 3 (mod 4) with (q|r₁) = +1, plus a 2-adic clause when 2 | a. But
> the class c also fixes a = (p+R₀)/4 modulo *every* prime ≤ q, so it
> can **force** small primes to divide a; a single forced ℓ with
> (ℓ|r₁) = −1 empties the counted family, and then "≫ x/(log x)^{3/2}"
> is a lower bound on the empty set. Verified counterexample: q = 23,
> R₀ = 35, r₁ = 7 passes the old test — (23|7) = +1, and R₀ ≡ 3 (mod 8)
> with p ≡ 1 (mod 8) makes a odd, so the 2-adic clause is vacuous — yet
> every hard prime has p ≡ 1 (mod 3) while 35 ≡ 2 (mod 3), so 3 | a
> *always*, and (3|7) = −1. The family is empty on every such class
> (first members p = 320401, 499801, 712321, 742681, 830449, …; test
> `test_type_I_admissibility_vacuity_counterexample`). The repair adds
> the missing local conditions (A2)–(A3) below, and costs the
> availability claim two orders of magnitude. Two things were gained in
> exchange, and they are worth more than what was lost: the **norm-form
> bridge**, and the **sharpness of the first link** (Theorem 5.7). A
> separate referee objection — that the half-dimensional sieve cannot
> give *lower* bounds over primes at all — was checked and **failed**;
> see "the parity objection" below.

**The norm-form bridge (paper eq. (5.1), `eq:normform`).** The
conceptual point the old passage was missing. For a prime r ≡ 3 (mod 4)
and odd ℓ ≠ r, reciprocity gives (−r|ℓ) = (ℓ|r) — because (r−1)/2 is
odd — so, for r ∤ n,

    every prime factor of n is a QR mod r
      ⟺  −r is a square mod 4n
      ⟺  n is **primitively** represented by a binary quadratic form
          of discriminant −r

(the last step is the classical correspondence between representations
and square roots of the discriminant, Cox, *Primes of the Form x²+ny²*,
Lemma 2.5; −r is a prime discriminant, hence has a **single genus**, so
the whole class group participates and no genus-selection condition
intervenes). Consequences: r ≡ 3 (mod 8) forces the represented n odd;
r ≡ 7 (mod 8) allows n even. Verified numerically at R = 3 on all
39,391 hard primes p ≤ 2×10⁷: the character condition and primitive
representability by x²+xy+y² agree in **39,391/39,391** cases (22,490
hits, 0 mismatches); re-verified in the test suite for r = 3, 7, 11
(class number 1) and r = 23 (class number 3) —
`test_norm_form_bridge_equivalence`.

So the character-type (character-obstruction) failure families of this program
are **norm-form families**: families of shifted prime values represented
by binary quadratic forms. *That* — not "dimension 1/2" in the abstract
— is why a lower bound is available here at all, and why it is not
available at dimension 1 − 1/φ(R₀).

**The parity objection, and why it fails.** The natural objection is
that lower-bounding "prime p **and** a multiplicative condition on
(p+R)/4" is a prime-detection problem, hence parity-blocked absent
bilinear input. It is not, for two reasons. (i) Primality of p is an
**input** here, consumed as a level of distribution via
Bombieri–Vinogradov, not an output to be detected. (ii) At sifting
dimension κ = 1/2 the lower-bound sieve function satisfies
β(1/2) = 1, so the semilinear sieve gives nontrivial lower bounds for
any s > 1, i.e. sifting range z = x^{1/2−δ}. The founding application
of the half-dimensional sieve is itself **prime-indexed**: Iwaniec,
*Primes of the type φ(x,y)+A where φ is a quadratic form*, Acta Arith.
**21** (1972), 203–234, proves matching upper *and lower* bounds
≍ N/(log N)^{3/2} for #{p ≤ N : p = Bφ(ξ,η) + A}. (The abstract
machinery paper — Iwaniec, *The half dimensional sieve*, Acta Arith.
**29** (1976) — is the wrong citation for this statement and was the one
previously given here.) What defeats parity concretely is a character
identity, not bilinear input: since r₁ | R₀ and 4a = p + R₀ we have
a ≡ 4⁻¹p (mod r₁), so χ_{r₁}(a) = χ_{r₁}(p) = +1 is *pinned by the
class*. Survivors with exactly **one** large non-residue prime factor —
the term of the same order as the main term, which no sieve can remove —
are therefore impossible; only the two-large-non-residue-primes term
survives, and it is O((s−1)log(2s−1)) against a main term ≍ √(s−1).
(The old proof sketch here said "at most one unsifted factor, removed by
a switching argument", which describes exactly the situation in which
the argument *cannot* work; switching bounds the **two**-large-primes
term.)

**Theorem 5.7 (the first link is sharp) — new, unconditional, and
ladder-free.** For R ∈ {3, 7, 15},

    #{hard primes p ≤ x failing R}  ≍  x/(log x)^{3/2},

with the two bounds separately at R = 11 (≪ and ≫). Upper bound: the
κ = 1/2 case of the Fundamental-Lemma chain (Theorems E/F/G/H here =
paper Theorem 1.11). Lower
bound: at these residuals the exact criteria (Theorems A/A′/A‴) make
failure *equivalent* to an all-residue condition on the factors of
a = (p+R)/4, which by the bridge is primitive representability by a form
of discriminant −r (r = 3, 7, 15; at R = 15 the Jacobi condition plays
the role of the Legendre condition), so Iwaniec (1972) applies with the
hard-prime congruences (H1)–(H3) absorbed into A and B. At R = 11 the
case-(b) budget failures of Theorem A″ are not of this shape, whence
only the one-sided bounds.

Moreover **3/2 is the ceiling of the method, not an artifact**: by
Theorem S (paper Theorem 1.10) every failure-sufficient family forbids at
least φ(R)/2 − O(1) classes, i.e. has sifting dimension ≥ 1/2, so no
failure family is denser than x/(log x)^{3/2}; and families of dimension
> 1/2 lie past the sifting limit, where no lower-bound technology
exists at all. There is no weaker-exponent fallback: the exponent is
3/2 or nothing.

**Theorem 5.8 (ladder failure lower bound; the corrected P₁).** *Call a
class c (mod M, fixing q and R₀) **admissible** if R₀ has a prime factor
r₁ ≡ 3 (mod 4) with*

* *(A1) (q|r₁) = +1;*
* *(A2) (ℓ|r₁) = +1 for **every** prime ℓ ≤ q that the class forces to
  divide a — the clause missing from the old statement; ℓ = 2 and
  ℓ ∈ {3, 5, 7} (forced by (H1)–(H3)) and 11 ≤ ℓ ≤ q are all in scope,
  since M contains every prime ≤ q;*
* *(A3) either r₁ ≡ 3 (mod 8) with a odd, or r₁ ≡ 7 (mod 8) with a
  even.*

*On every admissible class,*

    #E₀(x; c)  ≥  #{p ≡ c ≤ x : every prime factor of (p+R₀)/4
                    is a QR mod r₁}  ≫  x/(log x)^{3/2}.

**Proof sketch.** Membership implies failure by Prop 2.1 at r₁: all
factors of a are QRs mod r₁ (q by (A1), the forced small primes by
(A2), the rest by definition), whence (a|r₁) = +1 and, by consistency
a ≡ 4⁻¹p (mod r₁), also (p|r₁) = +1 *for free* — so every divisor of
m² is a QR mod r₁ while the target has (−m|r₁) = (−1|r₁) = −1. For the
count, apply the bridge and Iwaniec (1972) with A = −R₀,
B = 4·∏_{ℓ ≤ q, ℓ | a} ℓ (resp. 8·∏ over odd ℓ in the even-a case) and
discriminant −r₁: (A3) is what makes the 2-adic constraint solvable,
(A2) is what makes the family nonempty, and the conditions at r₁ are
free by consistency. **One step is not a routine citation, and must be
recorded as such:** the sieve delivers representability by *some* form
of the discriminant — non-split primes occurring to even multiplicity —
whereas the bridge needs *primitive* representability, no non-split
prime at all. That upgrade is the content of
Fuchs–Hsu–Rickards–Schindler–Stange, *Primes represented by shifted
quadratic forms: on primitivity and congruence classes*,
arXiv:2504.20289 (to appear, Acta Arith.), who show it is neither
immediate nor always true. The cases used here fall under their
Theorem 1.1 — **except** the mixed 2-adic configuration (r₁ ≡ 7 mod 8
with a odd), which is outside the citable statement; see the exemplars
below. ∎

**Availability and exemplars (recomputed under (A1)–(A3)).** Over the
39,391 hard primes p ≤ 2×10⁷ with their selected first rungs:

| test | count | share |
|---|---:|---:|
| (A1) alone: R₀ composite with some r₁ ≡ 3 (mod 4), (q\|r₁) = +1 | 2,593 | 6.6 % |
| (A1)–(A3), with a **nonempty** family | 9 | **0.023 %** |
| of those: case A (r₁ ≡ 3 mod 8, a odd) / case B (r₁ ≡ 7 mod 8, a even) / mixed | 5 / 0 / 4 | |

The old "6.6 % of first rungs are half-dimensionally admissible"
statistic measured only (A1) — i.e. a set on which the theorem's
conclusion can be vacuous. The correct availability figure is
**0.023 %**. **Correction (census, PR #57):** the 93.4 % figure first
recorded here was misattributed. It is the share of first rungs with
**no candidate r₁ passing (A1) at all** (36,798/39,391 = 93.4 %); the
share with R₀ **prime** is **65.2 %** (25,700/39,391). Prime R₀ is a
strict subset of the no-candidate set: when R₀ is prime its only
prime factor is r₁ = R₀, and Theorem J forces (q|R₀) = (p|q) = −1, so
no admissible r₁ exists by construction — but composite R₀ can fail
(A1) too. Both figures now come from
`erdos_straus.burgess_scan admissibility` and the archive
`data/analysis/burgess_admissibility.json`.

A second definitional point from the same census: (A3) *exactly as
printed* (case A or case B) holds for 5 first rungs, while the
headline 9 counts the union with the *mixed* case (r₁ ≡ 7 mod 8, a
odd). The extended reading is the mathematically right one — mixed is
2-adically fine, since 2 ∤ a means ℓ = 2 imposes nothing, and the
true 2-adic clause is just the ℓ = 2 instance of (A2). What singles
the mixed case out is FHRSS-citability, not solvability; the paper
now says so. Archive keys: `nonempty_family` = 9,
`a3_as_printed` = 5. The two
smallest exemplars remain the two smallest *viable* classes:
p = 5,544,361 (q = 31, R₀ = 51, r₁ = 3, a = 31·61·733, all factors
≡ 1 mod 3) is case A and satisfies (A1)–(A3) — the only forced small
prime dividing a is q = 31 itself, with (31|3) = +1 (test
`test_type_I_failure_family_exemplar_is_admissible`); p = 5,505,361
(q = 37, R₀ = 91, r₁ = 7, a = 37·37199) is in the **mixed** 2-adic case
and is therefore *not* covered by the citable form of [FHRSS]. Both
fail, as the mechanism demands.

**What Theorem 5.8 buys, and what it does not.** Much less than the old
statement claimed. On an admissible class it gives, against
Hypothesis P, the two-sided bracket

    (log x)^{−(1/2 − 1/φ(R₀))}  ≪  #E₀/#Ẽ₀  ≤  1,

since Ẽ₀ ≍ x/(log x)^{1+1/φ(R₀)} (Theorem B₂) — but **only at rung 0
and only on that 0.023 % family**. Everywhere else, and in particular
whenever R₀ is prime, the bracket is **one-sided**: only the upper
bound #E₀ ≤ #Ẽ₀ is unconditional. Hypothesis P is therefore *not*
two-sidedly bracketed in general; saying so was part of the same error.
Nothing at all is known for rungs j ≥ 1 (the simultaneous condition at
two rungs is a two-form problem with no Iwaniec analogue). The
unconditional lower-bound statement with real reach is **Theorem 5.7**,
which needs no ladder, no admissibility, and no census; what Theorem 5.8
adds is that the same mechanism survives the passage to p-adapted
residuals where it survives at all.

Where the residual gap sits is unchanged in kind: closing
(log x)^{1/2 − 1/φ(R₀)} means making failures as common as *avoidance*,
not merely as common as the norm-form family. Dimension 1/2 with a
norm-form parametrisation is the one place the large-factor wall opens;
widening the crack to dimension 1 − 1/φ(R₀) is the parity obstruction in
its sharpest local form — and it is the single statement separating the
measured c_P ≈ 0.1 from a theorem.

#### The Ladder Hypothesis, and what it would give

**Hypothesis L.** There is an absolute C such that for every hard
prime p, some Legendre non-residue q of p and some rung
R ≡ −p (mod 4q) with R ≤ C (log p)^C admits a certificate.

Hypothesis L implies R_min(p) ≪ (log p)^C — far beyond every sieve
bound in this development, and (dropping the quantitative bound) it
*is* the conjecture for hard primes, now organized as: along the
q-ladder, each rung fails only by a budget event of empirical
probability ≈ 5–14 % per rung, decaying geometrically (82,808 → 1,295
→ 0 in the data). The route's open mathematical content is precisely
to bound budget failures along Burgess-selected ladders — a
structured, local question about exponent budgets in (Z/R)*, in
contrast to the unstructured "some residual works". Wall 1 of §2.8
(p-dependent branches) does not apply here: the ladder is
p-adapted by construction. What stands between the census and a
theorem is the same object as in the Verdict above: control of budget
failures, now localized to explicit two-parameter families.

### 2.11 The uniform chain (Theorem U), the ceiling, and the obstruction lemmas

The August 2026 research round (two independent deep dives on the two
walls; see §8's outlook for their charters) produced one new
unconditional theorem, a sharp ceiling for the whole method family,
and two obstruction computations that pin the walls down precisely.

**Theorem U (uniform chain; Theorem 4.5 of the paper).** There are
absolute ε, c > 0 and an (ineffective, Siegel–Walfisz) x₀ such that
for x ≥ x₀:

    #{hard primes p ≤ x : R_min(p) > ε·log log x} ≤ x·exp(−c(log log x)²).

Unconditional — no Hypothesis B, no Hypothesis P, no q(p). The key
realization, found independently by both dives: Theorem L₁ never
needed Hypothesis B's survivor-decay structure. Its conclusion is a
direct many-residual sieve event — the chain of Theorems F–H run over
a list growing with x — and the only obstruction was uniformity of
the constants. The audit shows the growth is affordable to lists of
length B = ε·log log x:

1. *Dimensions for every ω.* Theorem S(iii)'s Kneser bound is proved
   for general t = 2^ω − 1 involutions: failure at any admissible R
   forbids ≥ φ(R)/2 − 2^{ω−1} − 1 classes, dimension
   ½ − (2^{ω−1}+1)/φ(R) ≥ 0.44 beyond an absolute bound (since
   2^{ω(R)} = R^{o(1)}). The ω(R) ≤ 2 restriction of the old chain
   was an artifact of the sharpened (enumeration) tier. Total
   dimension over the list: κ ≥ 1 + B/10.
2. *Branches.* Failing supports per residual: ≤ 2^{φ(R)} crudely;
   branch × class count over the list: exp(O(B²)).
3. *Sieve.* Brun's sieve of order ≍ κ on integers in one progression
   mod lcm(840, ∏_{ℓ≤B} ℓ) = e^{O(B)}. No primality detected, so the
   remainder is trivial (level x^{1/10}, no Bombieri–Vinogradov).
   Mertens in progressions to moduli ≤ B needs Siegel–Walfisz —
   whence ineffectivity. (Ω)-constant O(B log B).
4. *Accounting.* Gain exp(−κL) ≈ exp(−BL/10) vs cost exp(O(B²));
   with B = εL the exponent is −εL²/10 + O(ε²L²) ≤ −εL²/20 for small
   ε. (L = log log x.)

Consequences: Theorem U delivers conditional L₁'s mild calibration
J = (log log x)² unconditionally, and with a *stronger* R_min bound
(ε log log x versus (log x)^{2+o(1)}·(log log x)²). Hypothesis B's
real content therefore begins past the ceiling: the θ-calibrations
J = (log x)^θ (θ > 2/3 passes Vaughan) remain genuinely conditional.

**The ceiling (Remark 4.6 of the paper; corrected in the branch
round).** exp(−c(log log x)²) is the frontier of Theorem U's crude
branch bound — and, as the §2.12 re-audit established, the branch
factor e^{Θ(B²)} is the ONLY binding wall: the class modulus e^{O(B)}
never multiplies the main term (the classes partition the sifted
integers and the per-class main terms resum), and the
Mertens/Siegel–Walfisz inputs remain valid for lists up to any fixed
power of log x at the already-paid price of ineffectivity. A poly(R)
branch classification therefore moves the ceiling itself (§2.12,
polylog tier); the method family's absolute ceiling is
exp(−(log x)^{1/2+o(1)}), still short of Vaughan's
exp(−c(log x)^{2/3}). What Theorem U adds over Vaughan is not density
but structure: explicit certificates at residuals of size
O(log log x) for almost every hard prime.

**Obstruction (i): budget failure is not a character event (Remark
5.13 of the paper).** At R = 11 (generator 2), the model
configurations with class set {2, 7} and multiplicities (1,1) vs
(4,2) have the same class set and the same product a ≡ 3 (mod 11) —
identical under every Dirichlet character mod 11 — yet reach
{0,1,2,4,5,6,7,8,9} vs all of Z/10 in discrete logs: the first misses
the target 8 = 2³ (the consistent target for p ≡ 1 mod 11), the
second attains it. Verified by direct computation. Since 97.5 % of
measured first-rung failures are budget-type, no character-based
machinery — the pretension dichotomy included — can see the dominant
failure mode. This closes the pretension route of §8's outlook
(NO-GO), and note the route was self-undercutting anyway: q ∣ a_j at
every rung by construction, suppressing the Lemma-N character mode.

**Obstruction (ii): weighted detection ⟺ Hypothesis P.** The
certificate detector is already maximally relaxed — any *divisor* in
the universal class certifies (Prop 2.2/Proposition 3), so
almost-prime weakenings of the detected object change nothing (unlike
Nath–Xie's setting, where parity sits on the detected form; here it
sits on the conditioning set E_j). And the first moment of any
Bonferroni/Selberg weighting over E_j is itself a failure count: the
scheme is equivalent, up to constants, to Hypothesis P. The parity
gap of Theorem 5.8 (the corrected P₁) is intrinsic to every relaxation
of this type — and by Theorem S it is a *ceiling*, not a limitation of
the chosen detector: every failure-sufficient family has sieve
dimension ≥ 1/2, so x/(log x)^{3/2} is the best any family argument can
reach (§2.10).
Levels of distribution are not the obstruction (all moduli ≤ x^{1/2−ε};
EH/GRH change nothing). This closes the almost-prime route (NO-GO on
the literal P→B replacement).

**Also available (not yet in the paper):** B₂⁺ — the two-sided proxy
ladder with uniform 1+o(1) ratio constants on truncated proxies,
concentrating all of Hypothesis B's unproved content into Hypothesis
P; and the observation that the p-adapted ladder is the *wrong*
unconditional vehicle (the large-q(p) tail costs exp(−cL/log L),
worse than every fixed log-power — the fixed chain dominates; even
under GRH the ladder only matches U up to log factors at this
calibration). The ladder's enduring value is structural (character-type
failure dead by construction, p-adapted certificates) and conditional
(the only frame whose measured inputs would push past the ceiling).

**What remains open on this axis:** the branch classification — now
formulated, half-solved, and re-audited in §2.12 (the earlier claim
here that the Siegel–Walfisz and Mertens walls would still bind was
wrong; the branch factor is the only binding wall). The
per-prime conspiracy (no individual p fails all rungs) remains
polylog-interval-Chowla-hard — out of reach of current technology.

### 2.12 The branch classification: Theorem M-kernel, Conjecture A, and the polylog tier

The August 2026 branch round (one exhaustive enumeration prong, one
proof prong, independent) settled the shape of Open Problem 2. Paper
counterparts: Theorems 4.7/4.8/4.10/4.11, Conjecture 4.9, §4.2
(`sec:branch`).

**Setting** (cyclic, prime R, d = R−1, discrete logs): support
S ⊆ Z/d∖{0} at budget 2, reach M(S) = Σ_{v∈S}{0, v, 2v} (p-budget
absorbed as one more summand); S fails for t if t ∉ M(S); maximal =
failing with every one-element extension succeeding.

**Proved (paper Thm 4.7 — count blow-up).** The count form of the
classification is FALSE: ≥ 2^{c√d} maximal failing supports exist for
t = −1 (complete-partition construction; verified to d = 400).
Containers — poly-many covering sets — are the only viable form.

**Proved (paper Thm 4.8 — kernel branch + lossless reduction).** If
Stab(M(S)) = H ≠ {0}: the projection of S∖H is a failing support in
Z/(d/|H|) for the projected target (≠ 0), S ⊆ (H∖{0}) ∪ pullback,
and maximal S must CONTAIN H∖{0}. Iterating: every failing support
of Z/d lies in ψ⁻¹({0} ∪ T′)∖{0} for a composed quotient ψ and an
APERIODIC maximal failing support T′ downstairs, container size
≤ ⌊d/2⌋−1 (exact bookkeeping (h−1)+h⌊(d̄−2)/2⌋ = d/2−1; support
bound extended to odd moduli for the quotients). Machine-checked: zero
container-law violations across all 87,009 maximal supports at every
modulus d ≤ 30 and every target (the nontrivial-stabilizer cases
among them all satisfy assertions (ii) and (iv)). The
problem reduces losslessly to aperiodic maximal supports.

**Proved (size spectrum).** Maximal failing supports exist at every
size scale from Θ(log d) (complete partitions ⇒ singleton-miss
reaches; lower bound k ≥ log₃ d − 2 via the maximality covering
relation) to d/2 − 1. "Maximal ⟹ large" is false.

**Proved (negative — slack rigidity).** Aperiodic failing supports
with |S| ≥ 3 are never Kneser-tight: near-critical Kneser /
small-doubling machinery is VACUOUS here. The governing mechanism is
exact covering by complete sequences. (Salvage: a run/gap
classification of critical pairs with 3-AP summands.)

**Conjecture A (paper Conj 4.9 — aperiodic window containers).**
Every aperiodic maximal failing support lies in a window container
C(K, W) = φ_K⁻¹({0} ∪ ū·[c̄, c̄+w−1])∖{0} of size ≤ ⌊d/2⌋−1 — a
coset-progression (subgroup K and progression direction coexisting).
The family has fewer than d³ members (kernel size × direction × window start × window length), each forbidding ≥ half the nonzero
classes (sieve dimension ½ preserved per branch). Evidence:
- exhaustive, all moduli d ≤ 30, ALL targets (87,009 maximal
  supports, zero violations; bound attained ⇒ optimal);
- independent enumeration prong: every maximal failing support at
  R = 19, 23, 31, 43, 47, 59 (counts 336 / 1,034 / 4,291 / 40,759 /
  93,897 / 495,782 — note these EXCEED the DP mask-state counts, so
  supports-as-branches was doubly dead) and at composite R = 15, 35,
  39 fits a two-sided coset-progression container of density ≤ ½;
  zero unstructured examples at nine moduli; the (Z/35)* ≅ (Z/39)*
  failure tallies are identical — the structure is group-abstract
  (container tie-break counts differ, 115 vs 110, an artifact of the
  minimal-container search);
- proved for the signed complete-partition family (windows with room
  to spare); singleton-miss symmetry 2Σv = 2t pins the windows;
- the coset component is necessary: {11,17,19,29} ⊆ Z/30 is a
  singleton-miss support in no short 1-D window but in a
  ⟨10⟩-window container of size 14 = d/2 − 1 (rank 2 is real).
The open core: chaining of punctured (cofinite) intermediate reaches,
where direction information degenerates — the non-Hajós
factorization pathologies of cyclic groups.

**Conditional container theorem (paper Thm 4.10).** Under Conjecture
A (all moduli, via the recursion-closed pullback of windows): every
failing support is contained in one of fewer than d³ window
containers of
size ≤ ⌊d/2⌋−1 — branch count per residual O(R³) instead of
2^{φ(R)}, dimension ½ intact.

**Payoff re-audit (paper Thm 4.11 + corrected Rem 4.6).** The
earlier three-walls claim was wrong: (1) the class modulus
M̃ = e^{O(B)} never multiplies the main term — the classes partition
the sifted integers and the per-class main terms resum; only the
remainder sees M̃, harmless to B ≤ (log x)^{1−ε}; (2)
Mertens/Siegel–Walfisz inputs are valid for the individual moduli
R ≤ B up to any fixed power of log x (price: the ineffectivity
already paid). The branch factor was the only binding wall. Under
Conjecture A the balance per residual is gain δ(1−θ)L vs cost
(3+c_M)θL with B = (log x)^θ, admissible for θ < δ/(3+c_M+δ) ≈ 1/9:

    all but O(x·exp(−(log x)^{c₀})) hard primes have
    R_min(p) ≤ (log x)^{c₀}    (c₀ ≈ 1/9; family ceiling c₀ < ½).

Quasi-poly fallback (d^{O(log d)} containers): exceptional set
x·exp(−exp(c√(log log x))) — still past every fixed (log log x)^A
tier. Vaughan's exp(−c(log x)^{2/3}) stays stronger in density at
every tier of this family (ceiling ½ < 2/3); the value is
certificates at polylog residuals.

**Repo artifacts:** `erdos_straus.branch_enum` (enumerator + minimal
window containers + census CLI), archive
`data/analysis/branch_maximal_supports.json`, tests. The research
memos (branch_theorem, branch_enumeration) are summarized above.

### 2.13 The Conjecture A round: β-vacuity, the parity floor, and the Hajós payoff

The August 2026 Conjecture A round (independent prover and hunter
agents) did not prove the conjecture, but it changed its standing on
every axis. Verdict headline: **no counterexample exists anywhere it
was feared** — and the feared mechanism is provably empty.

**β-vacuity (proved; paper Prop 4.12).** A Kneser-critical deletion
step of punctured (β) type forces the deleted element into
Stab(M(S)): for f ∈ F and the punctures x, y isolated, f − v = x
would give x − v = f − 2v ∉ A against isolation, so F − v = F. Hence
aperiodic maximal failing supports admit only window-type (α)
critical steps. The "β-chain" stratum — the open core named in §2.12
and the stated reason non-Hajós orders looked dangerous — is empty by
theorem. Machine-confirmed on 507,133 classified supports (zero β
steps). What remains open is the control of *non-critical*
(slack-consuming) steps: an exact-covering-efficiency question,
indifferent to the Hajós/non-Hajós divide.

**Parity floor (proved).** At odd moduli the miss set F always has
even size — singleton-miss supports do not exist at all. The odd-d
floor family is |F| = 2, auto-maximal, realized by signed complete
partitions, window-shaped. Alongside: the **halving-pressure
inequality** (maximality forces |F| ≤ (d+k+1)/2), which makes
Conjecture A decidable at each fixed support size — and proved for
all odd d at sizes k ≤ 4 by finite verification; the **deep-run
identity** (at the floor family at most two elements can be α-type,
direction pinned to Δ = 2(σ−t)); and **quotient invisibility** (an
aperiodic maximal failure is invisible in every proper quotient —
the prime-power case is genuinely two-scale). Floor-embedding is
refuted: general maximal supports do not reduce to floor supports.

**Verification state** (`data/analysis/conjA_verification.json`):
exhaustive at every modulus d ≤ 60 (all targets; 24.25M
orbit-weighted maximal supports) — the gap between the two prior
ranges is closed; **exhaustive at d = 72, the smallest non-Hajós
order** (all 11 orbits, 14.99M supports, 10¹¹ DFS nodes; worst
aperiodic container exactly at the bound, never over); exhaustive at
5 orbits each of d = 108/120 plus 2–3M samples on the rest; sampled
at every non-Hajós order to 240 (incl. supports seeded from explicit
aperiodic de Bruijn factorizations of Z/72); prover sweeps at all
odd d ≤ 45 ∪ {47, 49, 53, 59}. Zero violations anywhere; bound
attained by aperiodic supports repeatedly (optimal). One
methodological catch: the d ≤ 30 sweep of §2.12 had used a laxer
container class; it was re-verified under the strict recursion-closed
class of Conjecture 4.9 — holds. Count growth: log₂(#maximal)/√d ≈
2.6–2.8 at d = 31..72, matching the 2^{c√d} theorem.

**Hajós payoff (proved reduction; paper §4.2 closing).** d = R−1 is
a Hajós order ⟺ (R−1)/2 ∈ {1, p^a, pq, p²q, pqr}. A Chen-type P₃
count gives ≫ B/(log B)² such admissible residuals ≤ B — dense
enough that **Conjecture A restricted to Hajós orders yields Theorem
4.11 at the same exponent up to o(1)**. So the conjecture only needs
to hold where the group theory is tame (where every verified case
lives), and a hypothetical non-Hajós counterexample would leave the
polylog tier intact. (The pure prime-power thinning d = 2p^a is
Sophie-Germain-hard and NOT usable — the P₃ tier is the right one.)

**Honest remainder:** the window-concentration statement for
non-critical steps at the |F| = 2 floor, and the two-scale coupling
at prime powers — both obstructed for current tools, with the
obstruction documented (conjA_proof.md C14). Conjecture A is now:
massively verified including exhaustively at the first non-Hajós
order, with its dangerous mechanism eliminated by theorem, its
payoff needing only its tame cases, and its difficulty localized to
one covering-efficiency question.


## 3. Empirical validation

All statements tested against the complete per-prime solvability masks
(27 residuals × 1 587 581 hard primes).

| Claim | Test | Result |
|---|---|---|
| Theorem A (R=3 iff) | all 1 587 581 primes | exact, 0 disagreements |
| Theorem A′ manifests as pure character-type | 41 421 sampled R=7 failures | 100 % character-type, 0 budget-type |
| Prop 1 direction | classifier consistency | ✓ |
| Prop 3 (no factor in S_R(p) among failures) | every residual tested | 0 violations |
| κ = 1/2 decay for R=7 (Thm A′ + sieve) | binned fit | κ̂ = 0.539 |
| κ = 1/2 decay for R=3 | binned fit | κ̂ = 0.387 (short range; S–D lower-order terms) |

character-type share of failures by residual (sampled): R=7: 100 %, R=23: 96.6 %,
R=11: 89.7 %, R=47: 87.2 %, R=71: 82.1 %, R=31: 79.3 %, … down to
R=67: 33.5 %. Character obstruction dominates at residuals that are prime
or have small 3-mod-4 prime power structure; class misses (budget-type)
broadly grow with φ(R), though not monotonically (see the sampled list
above) — as expected, since hitting one specific class among φ(R) gets
harder while the character argument only sees the QR/NQR dichotomy.

---

## 4. The four critical primes

Exactly 4 of 1 587 581 primes have a *unique* working residual ≤ 107 — the
entire obstruction to a shorter covering list, one per hard class involved:

| p | unique R | p mod 840 | failure anatomy (26 failures) |
|---:|---:|---:|---|
| 8 803 369 | 107 | 169 | 12 character-type + 14 budget-type |
| 142 361 209 | 59 | 529 | 13 character-type + 13 budget-type |
| 287 567 281 | 83 | 1 | 13 character-type + 13 budget-type |
| 794 037 841 | 63 | 121 | 16 character-type + 10 budget-type |

The record prime p = 8 803 369 fails every residual below 107 **even
allowing R up to 400**; its a-values are anomalously smooth (at R = 107,
a = 3²·11²·43·47). Its escape requires both failure mechanisms in roughly
equal measure — it is not explained by the character obstruction alone, nor
by class misses alone.

*(This section is unchanged by the 10¹² census: it is an analysis of the
complete 10⁹ mask data, and the four critical primes remain the only
primes below 10⁹ with a unique working residual ≤ 107. What did change
at 10¹² is that 8 803 369 is no longer the **maximal**-R prime — three
primes near 10¹¹–10¹² need R = 111, see §5 — nor is 107 a unique value
any more. The critical-prime analysis would have to be recomputed on
10¹² mask data to say anything about that range; per-residual masks
exist only to 10⁹.)*

---

## 5. The distribution of minimal R, the gap {87, …, 103}, and the record break at 10¹²

Minimal-R distribution at 10⁹: R=3 covers 49.1 %, {3,7,11} covers 91.3 %,
R ≤ 23 covers 99.3 %. Full histogram in `data/analysis/dist_1e9.json`.

**The distribution at 10¹²** (all 1 175 215 396 hard primes; full table
in `data/hard_primes_1e12_minimalR.meta.json`): R = 3 covers 56.0 %,
{3, 7, 11} covers 94.6 %, R ≤ 23 covers 99.73 %, R ≤ 39 covers
99.99 %. The head share creeps up decade by decade (49.1 % → 54.4 % →
56.0 % for R = 3 at 10⁹ → 10¹¹ → 10¹²) and the tail thins
geometrically. The complete deep tail:

| R | 87 | 91 | 95 | 99 | 103 | 107 | 111 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| count at 10¹¹ | 8 | 3 | 5 | 1 | 1 | 1 | 0 |
| count at 10¹² | 40 | 5 | 12 | 4 | 5 | 4 | **3** |

**Two things resolved since the 10⁹-era analysis below was written.**

1. **The gap {87, 91, 95, 99, 103} filled** between 10¹⁰ and 10¹¹,
   as the model predicted (§6).
2. **The record R = 107 broke at 10¹²**, at R = 111. It had stood since
   p = 8 803 369 < 10⁷ — unmoved through 10¹¹, five orders of magnitude. The three
   primes with R_min = 111 are

   | p | p mod 840 | a = (p+111)/4 |
   |---:|---:|---:|
   | 119 945 383 009 | 529 | 29 986 345 780 |
   | 654 730 707 409 | 289 | 163 682 676 880 |
   | 761 403 297 769 | 289 | 190 350 824 470 |

   For each, every admissible R ≤ 107 fails and R = 111 certifies; the
   certificates are in `data/hard_primes_1e12_minimalR.tail.json` and
   were re-derived and exactly checked (4abc = p(bc+ca+ab)) with full
   minimality. The old record 107 also stopped being unique, acquiring
   170 230 867 921, 269 646 744 481 and 565 158 121 441.

   Note the direct consequence for §2: the fixed list {3, 7, …, 107} —
   which sufficed for every hard prime below 10¹¹ — is **not** a
   covering list at 10¹². This is one observed instance of the behaviour
   Theorem K (§2.9) makes generic under Dickson's conjecture.

*(The 10⁹-era analysis that made the prediction is kept below,
unedited, so that the prediction can be read as it was made.)*

**The gap needs no modular explanation.** Under the independence model
(Section 6), expected counts of primes with minimal R = 87, 91, 95, 99, 103
are 0.12, 0.03, 0.05, 0.01, 0.01 — all ≪ 1. Observing zero in each is the
default outcome. The same model reproduces the observed counts at
R = 75, 79, 83 (expected 0.28, 0.39, 0.17; observed 2, 1, 2) up to the
correlation factor discussed below.

**The record is the anomaly, not the gap.** Conditioned on a prime failing
every residual ≤ 83, the independence model gives it a 53 % chance of
landing at minimal R = 87 and only a 1.7 % chance of landing at exactly
107 (total mass at or beyond 107: 6 %). The
one deep-tail prime below 10⁹ landed at 107. Together with the smoothness of
its a-values, this marks the record prime as structurally atypical even
among deep-tail primes — consistent with strong positive correlation of
failures across residuals for primes with smooth shifted values.

---

## 6. Independence model, correlations, and the 10¹⁰/10¹¹/10¹² forecasts (all resolved)

*(Reading order: the model and its 10⁹ calibration come first; the
outcome subsections that follow are newest-first — 10¹², then 10¹¹,
then 10¹⁰.)*

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
QR conditions mod common prime factors r of different R; 9 of the 27
residuals share the factor 3).

**Forecast for the decade [10⁹, 10¹⁰]** (~12.6 M hard primes), using fitted
power laws f_R(x) = C_R (log x)^{−κ_R}:

- new primes with min R > 83: ≈1.1 expected (indep.) × correlation ≈ 3 ⟹
  **a few expected**;
- new primes with min R > 107 (record broken): 0.038 (indep.);
  with the ×30 deep-tail calibration ⟹ **order 1 — a genuine coin flip**.

Both were sharp, falsifiable predictions of the model, tested directly
by the 10¹⁰, 10¹¹ and 10¹² runs; the outcomes follow.

**The model's forward commitment about the record.** Combining the 6 %
mass at or beyond 107 per deep-tail prime with the fitted deep-tail
growth rate places the *first record-breaking prime* in the decade
[10¹¹, 10¹²]. This was the model's sharpest falsifiable call — sharper
than the gap-fill, which was a distributional statement on a handful of
points — and it was on the record before the 10¹² run.

**Outcome (10¹² run, 1 175 215 396 hard primes, all solved — verified by
2 350 431 sampled reconstructions plus all 118 210 tail entries R ≥ 43
with full minimality; `bad = 0`, `not_minimal = 0`):**

- **Record: BROKEN, in the predicted decade.** Max minimal R = 111,
  first attained at p = 119 945 383 009 ≡ 529 (mod 840) — that is
  1.199×10¹¹, just past the previous bound — with a = (p+111)/4 =
  29 986 345 780; every admissible R ≤ 107 fails for it. Three primes
  reach 111; 107 gained three more and is no longer unique. The 27-value
  list {3, …, 107} that had covered everything over five orders of magnitude stopped
  covering.
- **Deep tail: 19 → 73 primes** with R_min ≥ 87. Conditional landing
  distribution vs the model's §5 prediction (predicted / observed share
  of the 73):
  P(87) 0.53 / 0.548; P(91) 0.11 / 0.068; P(95) 0.22 / 0.164;
  P(99) 0.03 / 0.055; P(103) 0.05 / 0.068; P(≥107) 0.06 / 0.096
  (χ² ≈ 5.8 on 5 d.f. against a distribution fixed in advance — no
  parameters refitted). The largest single contribution is the
  R ≥ 107 cell, where the model slightly *under*-predicted; that is the
  same direction as the deep-tail positive correlation already
  documented above.
- **Honest reading.** The model is a heuristic, calibrated on 10⁹ data:
  independent per-residual failure with fitted rates plus one deep-tail
  correlation factor. It has now made two forward calls that came out
  right — the band {87…103} filling (at 10¹¹) and the decade of the
  record break (at 10¹²). The first had little discriminating power
  (χ² ≈ 1.3 on 19 points, several expected cells below 5); the second is
  the substantive one, because "which decade does a long-static
  record fall in" is a single sharp bit that the model committed to and
  got. It remains a heuristic: nothing here is a theorem about R_max,
  and Theorem K (§2.9) is the only statement in this file about the
  record growing without bound — and it is conditional on Dickson.

**Outcome (10¹¹ run, 128 671 219 hard primes, all solved — verified by
sampling plus full tail checks; exhaustive below 10⁹):**

- **Record: HELD again** — max minimal R = 107, still uniquely at
  8 803 369, now across 5×10⁷ → 10¹¹. (It fell immediately past this
  bound: see the 10¹² outcome above.)
- **Gap: FILLED**, exactly as this model predicted. Minimal
  R ∈ {87, 91, 95, 99, 103} acquired 8, 3, 5, 1, 1 primes respectively,
  all in (1.3×10¹⁰, 10¹¹). Conditional landing distribution for the 19
  deep-tail primes (R_min > 83) vs the model's §5 prediction:
  P(87) predicted 0.53, observed 8/19 ≈ 0.42; P(91) 0.11 vs 3/19;
  P(95) 0.22 vs 5/19; P(99) 0.03 vs 1/19; P(103) 0.05 vs 1/19;
  P(≥107) 0.06 (of which exactly-107 ≈ 0.02) vs 1/19 (the record
  itself). The "gap" §5 explained
  statistically has now confirmed the explanation by disappearing.

**Outcome (10¹⁰ run, 14 215 707 hard primes, all solved):**

- **Record: HELD.** Max minimal R remains 107, still uniquely at 8 803 369.
  The coin flip resolved "no new record" — consistent with the independence
  estimate (0.038) and mildly against the ×30-corrected one (~1), suggesting
  the deep-tail correlation is driven by *per-prime* structure (smooth
  shifted values at one p), which becomes rarer as p grows, rather than by
  a persistent enhancement of the tail rate. **That inference did not
  survive 10¹²**: the deep tail grew 19 → 73 and the R ≥ 107 cell came
  in *above* the model's share (0.096 vs 0.06). The 10¹⁰ non-record is
  better read as one draw of a low-probability event than as evidence
  that records are suppressed.
- **Gap: PERSISTS.** Minimal R ∈ {87, …, 103} still unpopulated.
- Moderate tail as predicted: minimal R ∈ {75, 79, 83} grew 2, 1, 2 →
  3, 11, 5 (14 new primes; the model expected a handful).
- The four critical primes remain the only primes with a unique working
  residual ≤ 107 in the 10⁹ mask data; no prime below 10¹⁰ requires
  R > 107.

---

## 7. Covering sets at 10⁹

- Occurring minimal residuals: 22 values
  {3, 7, …, 83} ∪ {107} (all R ≡ 3 mod 4 up to 83, plus 107).
  (By 10¹² the gap has closed and the range has extended: **all 28**
  admissible values 3, 7, …, 111 occur as a minimal R, each with
  positive count — see §5.)
- Smallest covering list found (greedy over full masks): **18 residuals** —
  {3, 11, 15, 19, 23, 31, 39, 47, 59, 63, 71, 79, 83, 87, 95, 99, 103, 107};
  restricting candidates to the 22 occurring values also yields an
  18-element cover.
- Rigorous lower bound via disjoint-mask packing: **12** (12 primes with
  pairwise disjoint option sets exhibited). True optimum ∈ [12, 18].

---

## 8. What would close the hard cases

1. **Finite covering — resolved in direction.** Under Dickson's conjecture
   every fixed finite list fails infinitely often (Theorem K, §2.9) —
   and one such failure has now been observed: {3, 7, …, 107}, a
   covering list for every hard prime below 10¹¹, fails for three primes
   below 10¹² (§5); the
   sieve (Theorem D) gives density-(log x)^{−A} exceptional sets for every
   A but cannot reach emptiness. By completeness (R_min ≤ 2p ⟺ ESC), any
   unconditional bound on R_min is the conjecture itself.
2. **More exact criteria / longer chains.** ~~R = 11.~~ **Done** (A″,
   §2.6). ~~Lemma S at 19, 23.~~ ~~At 31…107.~~ **Done** (subset-DP,
   §2.7). ~~Composite residuals (R = 15 first).~~ **Done** — Theorem A‴
   (§2.6): a clean Jacobi-character dichotomy, no budget cases; general
   engine `solvable_exact_general` exact on every composite residual
   tested. ~~Lemma S past 107.~~ ~~Olson-type additive combinatorics.~~
   **Both done at once** — Theorem S (§2.7): Kneser's addition theorem
   proves the support bound for every residual unconditionally; the
   chain reaches exponent 1 + |P|/2 for arbitrary finite admissible
   lists (31/2 for the 27-residual list ≤ 107 with the aggregate
   families). Remaining on this axis: Conjecture A — the aperiodic
   window-container classification of §2.12 (kernel case proved,
   count form refuted there), whose resolution yields the polylog
   tier R_min ≤ (log x)^{c₀}.
3. ~~**Understand deep-tail correlation.**~~ **Done** — Theorem J (§2.9):
   joint character failure is controlled by one Legendre coin (p|q) per
   distinct prime of the interval factorizations; smoothness = fewer
   coins; the record prime is an extreme value of that statistic (no
   significance level attached — it was selected for being the record);
   pure-character-type record growth ≍ log x/log log x, consistent with
   the observed move 107 → 111 between 10¹¹ and 10¹². Remaining here:
   fold the budget-type escape layer into the growth law quantitatively.

### Research outlook (August 2026) — executed; see §2.11

Both routes sketched here were pursued to a decision in the same
month. **Conspiracy wall / pretension route: NO-GO**, with a
proof-grade witness — budget failure (97.5 % of the failure
population) is invisible to characters (§2.11, Obstruction (i)); the
plausibility argument below was self-undercutting since q ∣ a_j at
every rung suppresses the Lemma-N character mode. **Parity wall /
almost-prime route: NO-GO** on the literal P→B replacement — the
detector is already maximally relaxed and the weighted scheme is
equivalent to Hypothesis P (§2.11, Obstruction (ii)). **Both dives
converged on the same open door instead**: Hypothesis B was never
needed for the mild calibration, and the uniformity audit of the
chain produced the unconditional Theorem U (§2.11) with the ceiling
exp(−c(log log x)²). The original honest caveat stands, sharpened:
neither route — nor any relaxation examined — approaches the full
conjecture; parity (Hypothesis P's log-gap) and the per-prime
conspiracy (polylog-interval-Chowla-hard) remain the two walls.

---

## Appendix: reproduction

```bash
# full battery (Theorem A validation, taxonomy, fits, model, critical primes)
python -m erdos_straus.theory --masks data/analysis/residual_masks_1e9.json.gz

# Theorem A' finite verification alone (fast)
python -c "from erdos_straus.theory import verify_R7_finite; print(verify_R7_finite())"

# Theorem A''' (R = 15): finite enumeration, then validation vs ground truth
python -c "from erdos_straus.theory import verify_R15_finite; print(verify_R15_finite())"
python - <<'EOF'
import gzip, json
from erdos_straus.theory import validate_R15_criterion
with gzip.open("data/analysis/residual_masks_1e9.json.gz", "rt") as f:
    masks = {int(k): int(v) for k, v in json.load(f).items()}
print(validate_R15_criterion(masks))
EOF

# Theorem S: strong (Kneser) support bound, cyclic + general abelian forms
python -c "from erdos_straus.theory import verify_support_bound_strong as v; print(v(31))"
python -c "from erdos_straus.theory import kneser_support_general as k; print(k(15)); print(k(35))"
```
