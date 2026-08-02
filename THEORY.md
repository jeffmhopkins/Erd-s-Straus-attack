# Erdős–Straus, Hard Primes: Obstruction Theory for the Residual Method

**Date:** 2026-08-02.
**Status:** Theorems A, A′, A″, E, the meta-theorem, and Propositions 1–3
are proved (A′/A″ by machine-verified finite case analysis, reproducible via
`erdos_straus.theory`). Theorem D is proved modulo standard sieve machinery,
with the dependence stated. Section 6 is heuristic and is validated against
the complete solvability data for all 1 587 581 hard primes below 10⁹
(`data/analysis/residual_masks_1e9.json.gz`) and the 10¹⁰ minimal-R map.

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

## 2.5 Theorem E ({3,7} covering, unconditional): full proof

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
Friedlander–Iwaniec Lemma 6.3) with sifting range z = x^{1/10} gives

    |E(x)|  ≪  x · Π_{7 < q ≤ z} (1 − ω(q)/q)
            ≍  x · Π_{q≤z}(1 − 1/q) · Π_{q ≡ 2(3), q≤z}(1 − 1/q)
                 · Π_{q NQR(7), q≤z}(1 − 1/q)
            ≍  x · (log z)^{−1} · (log z)^{−1/2} · (log z)^{−1/2}
            =  x (log z)^{−2}  ≍  x (log x)^{−2},

using Mertens' theorem and its arithmetic-progression form. ∎

**Empirical confirmation.** The proportion of hard primes failing both
residuals should decay as C/log x. Measured from the complete 10⁹ masks, the
product (relative density) × (log x) is constant to within 2 % across three
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

## 2.6 The meta-theorem and the exact criterion for R = 11

### Meta-theorem (finite-state exact criteria)

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
R = 7 has 9 states (3 success / 3 all-even-fail — Theorem A′ re-derived),
R = 11 has 25.

### Theorem A″ (exact criterion for R = 11, hard primes)

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
**no state fails by a proper-subgroup obstruction**: the only subgroup of
(Z/11)* of even index containing a non-residue is {±1}, and the consistency
relation forces p's class to generate the rest.

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

---

## 2.7 Theorems F and G: exponents 5/2 and 3

The exponent bookkeeping to keep straight: each residual with an
exact-criterion-grade handle contributes sifting density **½** (its failure
forbids half the unit classes on its shifted form), and primality of
p = 4n − 3 contributes 1. Three residuals therefore give dimension 5/2 —
**not 3**; exponent 3 requires a fourth residual. Both theorems below are
now fully proven.

### Lemma S (support bound; machine-verified for R = 19, 23)

*Let R ∈ {19, 23}. Every configuration for which residual R fails at a
hard prime has at most (R−3)/2 nonzero factor-class support; equivalently,
the prime factors of (p+R)/4 lie in at most (R−1)/2 of the R−1 unit
classes mod R. Hence failure at R forbids at least half the classes, and
the failing configurations fall into finitely many maximal-support
branches, each a sifting condition of dimension ≥ ½ on (p+R)/4.*

**Proof.** Reachability of the target class is monotone in both the
support and the multiplicities. It therefore suffices to check that for
every support of size (R−1)/2 over the nonzero logs and every class of p,
the target is reachable already at minimal multiplicities. Exhaustive
check (`theory.verify_support_bound`): **437,580** pairs at R = 19 and
**7,759,752** pairs at R = 23 — zero failures. The bound is tight: Type-I
(all-QR) configurations occupy exactly (R−3)/2 nonzero classes. ∎

### Theorem F ({3,7,11}; exponent 5/2)

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

### Theorem G ({3,7,11,19}; exponent 3)

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

### Theorem G′ ({3,7,11,19,23}; exponent 7/2)

*Identically, with Lemma S at R = 23 and the form (p+23)/4 = n+5:
the joint exceptional set of {3, 7, 11, 19, 23} is O(x/(log x)^{7/2}).*

**The chain — completed to R = 107.** Every further prime residual
R ≡ 3 (mod 4) whose support-bound lemma is verified adds ½ to the
exponent. The naive verification cost is C(R−2, (R−1)/2) reachability
checks, which explodes past R = 31; but a **subset dynamic program**
(`theory.verify_support_bound_dp`) folds all supports into a table
mapping each reachability mask to the maximal support size achieving it
(valid because failure at any multiplicities implies failure at
multiplicity 1, by monotonicity). Realized masks are heavily structured,
so the state count stays tractable:

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

**Theorem H (the full prime chain).** *Let
P = {3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107} — all
fifteen primes ≡ 3 (mod 4) up to 107. The number of hard primes p ≤ x
failing every residual in P is O(x/(log x)^{17/2}); all but a proportion
O((log x)^{−15/2}) of hard primes are solved within P.*

Proof: identical to Theorem G — the forms (p+R)/4 = n + (R−3)/4 are
distinct integer shifts of n; Theorems A/A′/A″ handle 3, 7, 11 and
Lemma S (now verified for the twelve remaining primes in P) handles the
rest; each contributes dimension ≥ ½ through finitely many
maximal-support branches, plus 1 for primality: total ≥ 1 + 15/2. ∎

### Theorem I (aggregate identity families) and the 19/2 upgrade

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

**Sieve consequence.** Failure of both families means p+1 and p+4 (two
new linear forms, ~(2n−1) and (4n+1) in n = (p+3)/4) are free of primes
≡ 3 (mod 4): two further sifting conditions of dimension ½ each. Added
to Theorem H: *the number of hard primes p ≤ x failing all fifteen prime
residuals up to 107 **and** both aggregate families is
O(x/(log x)^{19/2}).*

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

## 2.8 Two attempts at totality, and their walls

Both attempts below were executed; each yields something real, and each
hits a wall that is now *precisely characterized* rather than merely
suspected.

### Attempt 1 (constructive): aggregate families

Outcome: Theorem I above — the complete list of a-independent divisor
identities is {p+1, p+4}; they cover 74 % of hard primes and add +1 to
the chain exponent. Wall: any family of this shape covers p through a
multiplicative condition on a *single shifted value*, so its failure set
has density ~(log x)^{−1/2} — positive at every finite level. The four
critical primes already escape both families. Constructive families
thicken the almost-all coverage but structurally cannot reach totality.

### Attempt 2 (analytic): growing lists and the larger sieve

Idea: let the residual list grow with p (B ≈ C log p), so the sieve
dimension grows and the count bound x/(log x)^{κ(B)} could in principle
drop below 1 — proving R_min(p) ≤ C log p outright. Two requirements
emerge:

1. **p-independent forbidden classes.** The per-branch half-density
   forbidden sets of Lemma S depend on p mod R; aggregating them over
   ~log x residuals requires conditioning on p mod ∏R ≈ e^{B/2} ≈ x² —
   more classes than there are primes ≤ x. Only *p-independent* (branch-
   and p-class-free) forbidden classes can be aggregated. Computing this
   set exhaustively (forced-class DP over all configurations and all p
   classes, R = 11 … 43): **the always-forbidden set is exactly one
   class — the universal class −4⁻¹ (mod R) — at every R tested.** Every
   other class occurs in some failing configuration. So the aggregable
   sifting weight per modulus q is W(q) = #{R ≤ B : R | 4q+1}, of average
   ~½ log B — not the ~B/log B that half-density sets would give.

2. **The support-level cap.** Even granting stronger inputs, the larger
   sieve's quantity L is capped by the constraint d ≤ Q: moduli usable
   for the growing list have size ≥ B, so at most log Q/log B ≈
   log x/(2 log log x) of them fit into one squarefree d, giving
   L ≤ exp(O(log x/log log x)) — never ≥ x. The same cap appears as the
   remainder-term explosion (log x)^{#forms} in the fundamental lemma.

Outcome: unconditionally the growing-list route yields at best a bound
of shape x·exp(−c(log log x)²) — beyond every fixed power of log, but
(a) still divergent, and (b) weaker than Vaughan's classical
x·exp(−c(log x)^{2/3}). The wall is not technical laziness: it is the
collapse of the p-independent forbidden structure to a single class,
measured exactly by the AF computation.

### Verdict

Upper-bound counting — fixed lists, growing lists, aggregate families,
in any combination available to us — bounds the exceptional set but
cannot empty it. The residual method's genuine frontier is an existence
statement (some R ≤ f(p) works for *every* p), which no upper-bound
sieve can deliver. Candidate genuinely-new inputs, in increasing order
of speculation: (i) additive-combinatorial theorems (Olson-type bounded
subset sums in cyclic groups) proving failing supports at every R are
either small or subgroup-trapped — this would enlarge the *provable*
forbidden structure and could push the conditional bound past Vaughan;
(ii) bilinear/dispersion estimates treating p and the factors of p+R
symmetrically; (iii) a mean-value treatment of the certificate count
itself (the Vaughan route) upgraded with the residual structure.

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

**Outcome (10¹⁰ run, 14 215 707 hard primes, all solved):**

- **Record: HELD.** Max minimal R remains 107, still uniquely at 8 803 369.
  The coin flip resolved "no new record" — consistent with the independence
  estimate (0.038) and mildly against the ×30-corrected one (~1), suggesting
  the deep-tail correlation is driven by *per-prime* structure (smooth
  shifted values at one p), which becomes rarer as p grows, rather than by
  a persistent enhancement of the tail rate.
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
2. **More exact criteria / longer chains.** ~~R = 11 as the first Type-II
   case.~~ **Done** (Theorem A″, §2.6). ~~Sieve-grade handles on 19, 23.~~
   **Done** (Lemma S, §2.7) — note the support-bound lemma suffices for
   the sieve without the full exact criterion. Proven exponents: 5/2
   ({3,7,11}), 3 ({3,7,11,19}), 7/2 (adding 23). Next: bit-parallel
   verification of Lemma S at R = 31, 43, 47 (exponents 4, 9/2, 5), and
   the first composite criterion R = 15 (coupled conditions mod 3, mod 5).
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
