# Lean formalization

Machine-checked (Lean 4.32.2 + mathlib) formalization of the core
residual framework from the companion paper. The working-letter ↔
paper-number dictionary is THEORY.md's mapping table (§1).

## Verified (sorry-free; audited by `#print axioms`)

| Declaration | Paper counterpart |
|---|---|
| `certificate_sound` | §1.1: a factorization k·k′ = m² with R·b = k+m, R·c = k′+m yields the Erdős–Straus identity 4abc = p(bc+ac+ab) |
| `certificate_integrality` | §1.1: R ∣ k+m and gcd(R,k)=1 force R ∣ k′+m, so b, c are integers |
| `reciprocity_structure` | Theorem J: (q\|R) = (p\|q) for odd primes q ≠ R with R ≡ 3 (mod 4), q ∣ p+R |
| `theoremA_necessity` | Theorem A (⇒), p ≡ 1 (mod 3): all prime factors of a ≡ 1 (mod 3) blocks every divisor k of (pa)² from the class −pa (mod 3) |
| `theoremA_sufficiency` | Theorem A (⇐), p ≡ 1 (mod 3): a divisor q ≡ 2 (mod 3) of a yields positive b, c with the identity (k = q) |
| `theoremA_two_mod_three` / `exists_factor_two_mod_three` | **Theorem A, the p ≡ 2 (mod 3) case** — the other half of the paper's Theorem 1.2 (all 3 ∤ p): residual 3 succeeds unconditionally there (4a = p+3 forces a ≡ 2 (mod 3), so k = a is a divisor of m² in the target class), with explicit positive b, c and no factorization hypothesis; `exists_factor_two_mod_three` shows the paper's criterion is automatic in that case. Together with the two rows above, Theorem A is now formalized for **every** hard-prime congruence class mod 3 |
| `divisor_one_mod_three` | the multiplicative-closure lemma behind necessity |
| `composite_reciprocity` | Lemma 5.1 (Lemma J°): (q\|R) = (p\|q) with the left symbol Jacobi, for any R ≡ 3 (mod 4) — prime or composite — and odd prime q ∣ p+R (the paper's gcd(q,R)=1 hypothesis turns out unnecessary) |
| `jacobi_necessity` / `divisor_jacobiSym_one` | Lemma 5.2 (Lemma N): if every prime factor of a has Jacobi symbol +1 mod R, no divisor k of (pa)² lies in the class −pa (mod R) — via the Jacobi analogue of the multiplicative-closure lemma |
| `selected_residual_nonresidue` | selected residual, §5.1: with (p\|q) = −1 and 4q ∣ p+R (as at R₀ = (−p) mod 4q and every ladder rung), (q\|R) = −1 — the all-residue failure mode of Lemma N is impossible at R by construction |
| `family_p_plus_one` | Proposition 1.12 (Theorem I in the notes): R ∣ p+1 certifies via k = a·p² — identity, integrality **and positivity**: under 0 < p, 0 < R the theorem concludes 0 < b ∧ 0 < c |
| `family_p_plus_four` | Proposition 1.12: R ∣ p+4 (R odd) certifies via k = a²·p — identity, integrality **and positivity** (0 < b ∧ 0 < c under 0 < p, 0 < R) |
| `hard_classes_are_squares` | the six Mordell classes are squares of units mod 840 (explicit witnesses 1², 11², 13², 17², 19², 23²) |
| `hard_classes_local` | Corollary 2.3(i)'s arithmetic core: hard classes ≡ 1 (mod 8), ≡ 1 (mod 3), QR mod 5 and mod 7 |
| `reach` / `powers` / `step` | the meta-theorem's finite model: divisor-class reachability from (class, exponent-budget) pairs, computably, in ZMod R |
| `reach_mono` | Lemma 4.1 (monotonicity reduction), budget half: entrywise larger exponent budgets enlarge the reachable set |
| `reach_sublist` | Lemma 4.1, support half: dropping factor classes shrinks the reachable set |
| `isOfFinOrder_of_isUnit` / `powers_saturate` / `powers_congr_saturated` / `step_congr` / `reach_congr` / `reach_cap_saturate` / `reach_cap_entry` / `reach_mult_cap` | **the multiplicity cap is lossless** (the meta-theorem's cap, Remark 2.6): once an entry's exponent budget reaches `orderOf x − 1` its power set is the whole cyclic subgroup `⟨x⟩`, so `reach` is invariant under any further budget increase — `reach_mult_cap` concludes that for `orderOf x ≤ 2c+1` (true at `c = ⌈(R−1)/2⌉` for every unit class) a multiplicity μ ≥ c reaches exactly what the capped multiplicity c reaches. This is what makes the *capped* finite enumerations below exhaustive rather than under-approximations |
| `theoremA'_finite_R7` | Theorem A′'s finite verification: all 1,536 consistent capped hard-prime configurations at R = 7 (384 after collapsing the neutral class), stated in the multiplicative `reach` model — target −m reachable ⟺ a non-residue class is present (`native_decide`) |
| `rot18` / `lemmaS_finite_R19` | Lemma S at R = 19: every 9-class support reaches the target at minimal multiplicities, for every class of p — C(17,9) = 24,310 supports × 18 = 437,580 checks, stated in the discrete-log coordinates of the proof (`native_decide`) |
| `rot10` / `theoremA''_finite_R11` | Theorem A″'s finite verification: all 497,664 consistent capped configurations at R = 11 — target reachable ⟺ neither failure shape (all-QR, or the three exact budget patterns), in discrete-log coordinates (`native_decide`) |
| `rot22` / `lemmaS_finite_R23` | Lemma S at R = 23: C(21,11) = 352,716 supports × 22 = 7,759,752 checks, same form as R = 19 (`native_decide`) |
| `rotg` / `maskSet` / `mstep` (Bridges.lean) | the parametric discrete-log bridge: a mask represents a set of classes, rotation is multiplication by g^s (`maskSet_rotg`), the mask fold is `reach` (`maskSet_mstep`, `reach_eq_maskSet`) — standard axioms only |
| `reach_perm` / `reach_append_single` | `reach` is invariant under permutations of the configuration list (step is right-commutative) |
| `lemmaS_finite_R19_mult` / `lemmaS_finite_R23_mult` | the support bounds **restated over `ZMod 19` / `ZMod 23` and the multiplicative `reach` model** (any duplicate-free enumeration of any 9- resp. 11-class support), derived from the mask checks via the bridge |
| `theoremA''_finite_R11_mult` | Theorem A″'s exact criterion **restated over `ZMod 11`** — class-indexed multiplicities, consistency-determined p, reach membership ⟺ neither failure shape — derived via the bridge |
| `IsSubprod` / `mem_reach_iff_subprod` (DivisorBridge.lean) | `reach` computes exactly the classes of bounded-exponent integer subproducts |
| `isSubprod_primes_iff_dvd` | subproducts of a prime list (budget 1 per occurrence) are exactly the divisors of its product — the fundamental theorem of arithmetic in the form the model needs |
| `mem_reach_iff_dvd` / `divisorConfig` | **the divisor bridge**: c ∈ reach(factor configuration of N) ⟺ ∃ k ∣ N with class c |
| `reach_certificate` / `certificate_reach` | **the meta-theorem's reduction, capstone**: reach membership of the target −m (m = p·a, 4a = p+R) yields explicit positive k ∣ m², b, c with R·b = k+m, R·c = m²/k+m and 4abc = p(bc+ca+ab) — and conversely every divisor class is reached. Reach membership of a class ⟺ existence of a divisor of m² in that class, machine-checked; reach membership of the target yields the explicit certificate |
| `reach_merge` / `reach_subperm` / `reach_two_eq_doubled` | budget consolidation: equal-class entries merge with summed budgets, reach is monotone under sub-permutations, budget-2 = doubled budget-1 |
| `lemmaS_R19_certificate` | **the composed corollary**: if `(p+19)/4` has nine prime factors in pairwise-distinct unit classes ≠ 1 mod 19, an explicit Erdős–Straus certificate exists at p — enumeration + both bridges + consolidation, end to end |
| `R31.dedupMax_dominates` / `R31.dp_sound_aux` (LemmaS31.lean) | **verified dynamic programming**: the DP round carries every state and adds every extension; the soundness induction shows every support `S ⊆ {1..29}` is represented with count ≥ min(\|S\|, 15) — standard axioms only |
| `R31.lemmaS_finite_R31` | **Lemma S at R = 31**: the C(29,15) = 77,558,760 supports are *never enumerated* — the DP covers them through 3,001 states; the compiled evaluator runs the DP and the final 3,001 × 30 target check (`native_decide`), while the DP's correctness is proved, not trusted; result stays in mask coordinates (no `_mult` bridge yet) |
| `rot2` / `maskSet2` / `mstep2` (BridgeR15.lean) | the **product-index mask bridge** for non-cyclic unit groups: masks over `Fin d1 × Fin d2` flattened to `d1·d2`-bit naturals, rotation = componentwise block rotation; `maskSet2_rot2` (rotation = multiplication by `g^s·h^t`), `maskSet2_mstep2` (mask step = `step`), `reach_eq_maskSet2` (mask fold = `reach`), proved symbolically for any `R, d1, d2, g, h` with `g^d1 = 1`, `h^d2 = 1` — standard axioms only |
| `theoremA'''_finite_R15` | **Theorem A‴'s finite verification (R = 15**, the paper's Theorem 1.6): all 349,920 consistent capped hard-prime configurations over `(ℤ/15)* = ⟨11⟩ × ⟨7⟩ ≅ C₂ × C₄` (multiplicities 0..5 per class, class 2 forced, `p ≡ 1, 4 (mod 15)`, consistency `∏ = 4p`) — the target `11` is reachable **iff** some factor class has Jacobi symbol −1 mod 15 (i.e. lies in `{7, 11, 13, 14}`): 349,380 successes, 540 all-residue failures, **no budget failures** — in product-mask coordinates (`native_decide`) |
| `theoremA'''_finite_R15_mult` | Theorem A‴'s exact criterion **restated over `ZMod 15`** and the multiplicative `reach` model, derived from the mask check via the product-index bridge — inherits exactly the one `native_decide` axiom |
| `Finset.add_kneser` / `Finset.mul_kneser` (Kneser/, vendored) | **Kneser's addition theorem**: `#(s + H) + #(t + H) ≤ #(s + t) + #H` with `H = (s + t).addStab` — vendored unmodified from Yaël Dillies' misc-yd (Apache 2.0, attribution in the file headers); standard axioms only |
| `add_kneser_list` (TheoremS.lean) | **iterated Kneser**: for a family `A₁, …, A_k` with `H` the stabilizer of `∑ Aᵢ`, `∑ #(Aᵢ + H) ≤ #(∑ Aᵢ) + (k−1)·#H` — induction replacing the head summand `B` by `B + H`, whose key step is `(t + H).addStab = H` |
| `theoremS_support_bound` | **Theorem S (paper Theorem 1.10(i))**: for even `d` and `S` a set of nonzero elements of `ZMod d`, if `M(S) = ∑_{v∈S} {0, v, 2v} ≠ ZMod d` then `#S ≤ d/2 − 1` — Kneser + trivial/nontrivial-stabilizer cases + the quadratic `h + d/h − 3 ≤ d/2 − 1`; the unconditional support bound behind Lemma S for *every* residual — standard axioms only |
| `theoremS_support_bound_odd` | **Theorem S at odd moduli** (the parenthetical of the paper's Theorem 4.8, needed for the kernel-branch quotients): for odd `d`, `M(S) ≠ ZMod d` forces `#S ≤ (d−3)/2` — no summand is degenerate at odd `d` (no 2-torsion), and in the nontrivial-stabilizer case both `h` and `d/h` are odd, so the endgame is `(h−2)(d/h−2) ≥ 1` |
| `reach2` / `budget2` / `Failing` / `MaximalFailing` (KernelBranch.lean) | the branch-classification vocabulary over any finite abelian group: the budget-2 reach `M(S) = ∑_{v∈S} {0, v, 2v}` (shared with Theorem S through `reach2_zmod`), failure `t ∉ M(S)`, and maximality (every one-element extension by a nonzero class attains `t`) |
| `target_notMem_reach2_add_addStab` / `projected_target_ne_zero` / `zero_notMem_projected_support` / `projected_failing` | **Theorem 4.8(i)** (kernel branch; lossless reduction): for `H = Stab(M(S))` and any hom `φ` with kernel exactly `H`, a failing target misses the whole saturation `M(S) + H`, the projected target `φ(t) ≠ 0`, the projected support `T̄ = φ(S \ H)` consists of nonzero classes, and `T̄` fails for `φ(t)` downstairs **at the same budget** — the reduction loses nothing (collisions only enlarge the reach, `reach2_image_subset`) |
| `addStab_erase_zero_subset_of_maximal` | **Theorem 4.8(ii)**: a *maximal* failing support contains every nonzero class of `H` — for `w ∈ H` the summand `A_w ⊆ H` stabilizes `M(S)`, so `M(S ∪ {w}) = M(S)` still fails |
| `container` / `support_subset_container` / `card_container_le` | **Theorem 4.8(iii)** and its size bookkeeping: `S ⊆ (H \ {0}) ∪ φ⁻¹(T̄)`, a container of at most `(h−1) + h·#T̄` elements (fibers of `φ` are cosets of `H`, `card_fiber_le`) |
| `addStabSubgroup` / `nsmul_card_addStab` / `exists_addStab_quotient` | **the quotient `φ_H : ZMod d → ZMod d̄`**: the stabilizer of a nonempty finset is a subgroup, Lagrange annihilates it, and reduction mod `d̄ = d/h` has kernel **exactly** `H` — the projection Theorem 4.8 reduces along, constructed (not assumed) |
| `kernel_branch_card_bound` / `kernel_branch` | **Theorem 4.8, one reduction step, packaged over `ZMod d`**: the container of a failing support has at most `⌊d/2⌋ − 1` elements — Theorem S downstairs in both parities (`theoremS_support_bound` at even `d̄`, `theoremS_support_bound_odd` at odd `d̄`, the `d̄ = 2` edge case being automatic since Theorem S forces `T̄ = ∅` there) plus the bookkeeping `(h−1) + h·⌊(d̄−2)/2⌋ ≤ d/2 − 1`, exact at even `d̄`. `kernel_branch` collects (i)–(iii) and the bound in one statement |
| `betaVacuity` / `punctured_of_compl` / `card_reach2_of_punctured` / `betaVacuity_aperiodic` | **Proposition 4.12 (β-vacuity)**: if the deletion step at `v` is Kneser-critical of *punctured* type (the complement of `M(S \ {v})` is the miss set plus two isolated punctures `x, y`, isolation being `x−v, y−v ∈ M(S \ {v})`) then `F − v = F`, i.e. `v ∈ Stab(M(S))`; `card_reach2_of_punctured` checks that the complement form is exactly criticality (`\|M(S)\| = \|M(S \ {v})\| + 2`), and `betaVacuity_aperiodic` is the "in particular": at an aperiodic failing support no critical deletion step is of punctured type — the feared chaining of punctured intermediate reaches is empty |
| `sums2` / `IsCompletePartition` / `sums2_of_completePartition` / `reach2_of_completePartition` / `completePartition_failing` | **the complete-partition lemma behind Theorem 4.7** (branch count blow-up): the budget-2 subset sums of a complete partition of `N` (parts largest first, each `≤ 1 +` the sum of the rest) are exactly the interval `[0, 2N]`, by induction on the parts; transported to `ZMod d` with distinct parts this makes the reach the image of `[0, 2N]`, so every class above `2N` is missed — the singleton-miss mechanism of the `2^{c√d}` construction |

Together these verify the elementary layer of the paper end to end —
certificates are sound and integral, Theorem A is exact in both
directions and now covers **both** hard-prime classes mod 3 (p ≡ 1 by
`theoremA_necessity` / `theoremA_sufficiency`, p ≡ 2 unconditionally by
`theoremA_two_mod_three` — together the paper's Theorem 1.2 for all
3 ∤ p), both aggregate identity families certify with **positive**
b, c (identity, integrality and positivity), the
reciprocity
identity governing joint failure is correct — including its composite
form and the ladder's elementary layer (Lemmas 5.1, 5.2 and the
selected-residual corollary, `Ladder.lean`) — and the hard-class local
structure is checked — plus the finite-enumeration layer: the
meta-theorem's reachability model with both monotonicity reductions,
the R = 7 check stated directly in that multiplicative model
(`ZMod 7`, no discrete-log encoding), the full R = 11
criterion
(Theorem A″'s exact two-case failure classification — capped, but the
cap is now proved lossless: `reach_mult_cap` shows that past the
saturation threshold `orderOf x − 1` extra multiplicity adds nothing,
so the capped enumerations are exhaustive, not under-approximations),
and the
R = 19 and R = 23 support-bound checks — the latter three evaluated
in the discrete-log coordinates their proofs use, **and then carried
back to the multiplicative model by the formally proved discrete-log
bridges** (`Bridges.lean`): the mask semantics (rotation =
multiplication by `g^s`, mask fold = `reach`) is a theorem, so
`theoremA''_finite_R11_mult`, `lemmaS_finite_R19_mult`, and
`lemmaS_finite_R23_mult` state the same results directly over
`ZMod 11 / 19 / 23` and `reach`, with no coordinate caveat left. The
same recipe now covers the non-cyclic composite residual R = 15
(`BridgeR15.lean`): the product-index mask bridge (`maskSet2_rot2`,
`reach_eq_maskSet2`, proved for any product decomposition
`g^d1 = h^d2 = 1`) carries the 349,920-configuration check of the
paper's Theorem 1.6 (`theoremA'''_finite_R15`) back to `ZMod 15`
(`theoremA'''_finite_R15_mult`) — the exact criterion is a pure
Jacobi-character dichotomy, with no budget failure shapes. And the
support bounds no longer stop at fixed residuals: `TheoremS.lean`
proves the paper's Theorem 1.10(i) (`theoremS_support_bound`) from
Kneser's addition theorem (vendored, `Kneser/`) via the iterated form
`add_kneser_list` — for every even `d`, a bounded subset-sum set
`M(S) ≠ ZMod d` forces `#S ≤ d/2 − 1`, symbolically, with no
enumeration at all — and `theoremS_support_bound_odd` extends it to
odd moduli (`#S ≤ (d−3)/2`), which is what the quotients of the branch
classification need. On top of that, `KernelBranch.lean` formalizes
the **kernel branch** of the branch classification (the paper's
Theorem 4.8): for a failing support with nontrivial stabilizer
`H = Stab(M(S))` the reduction along the quotient
`φ_H : ZMod d → ZMod d̄` — constructed here, `exists_addStab_quotient`,
not assumed — is *lossless* (the projected support fails downstairs
for a nonzero projected target, `projected_failing`), maximality
captures all of `H \ {0}` (`addStab_erase_zero_subset_of_maximal`),
the support is contained in the container `(H \ {0}) ∪ φ_H⁻¹(T̄)`, and
that container has at most `⌊d/2⌋ − 1` elements
(`kernel_branch_card_bound`, Theorem S downstairs in both parities).
The same module proves Proposition 4.12 (β-vacuity, `betaVacuity`):
a critical deletion step of punctured type forces the deleted class
into the stabilizer, so at an *aperiodic* maximal failing support the
punctured mechanism — the one failure mode previously feared for
Conjecture A — is provably empty. What is *not* formalized there is
the iterated Reduction Lemma (the strong induction on `d` composing
these single steps into a chain of quotients) and, of course,
Conjecture A itself.
Finally, the reach ⟺ divisor-certificate bridge
(`DivisorBridge.lean`) proves the model faithful to the integers:
`reach` membership of a class is existence of a divisor of `m²` in
that class (via the fundamental theorem of arithmetic), and reach
membership of the target `−m` produces an explicit positive
Erdős–Straus certificate (`reach_certificate`) — the meta-theorem's
reduction itself, fully symbolic, standard axioms only.

### Trust base

Every main theorem is audited by `#print axioms` (70 audit lines;
helper lemmas are covered transitively through the audited theorems). The model and the
monotonicity lemmas — and the whole Kneser / Theorem S / kernel-branch layer (`TheoremS.lean`, `KernelBranch.lean`) — report only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). The six finite checks (five enumerations plus the R = 31
`dp_check`) use `native_decide` and so additionally report a `..._native.native_decide.ax_1_1`
axiom (the `Lean.ofReduceBool` mechanism) — trust in the Lean
compiler and its evaluator, not just the kernel. Two engineering
notes, learned the hard way: kernel `decide` on `Finset`/`Multiset`
computations (quotient lifts, dedup) does not terminate in reasonable
time even on the 384-case R = 7 space; and evaluating the R = 19
check in the `Finset`-over-`ZMod` model costs hours in the
interpreter, while the same enumeration in discrete-log mask
coordinates (pure `Nat` bit arithmetic, as in
`theory.verify_support_bound`) runs in seconds — which is why
the log-coordinate checks are *evaluated* in those coordinates. The
coordinates themselves add no trust: `Bridges.lean` proves the mask
semantics symbolically (standard axioms only) and derives the
multiplicative `_mult` forms, each of which reports exactly its
enumeration's single `native_decide` axiom beyond the three standard
axioms — no additional computational trust.
Mitigation for the evaluator trust: every enumeration is checked by
independent Python verifications of the same criteria
(`theory.verify_R7_finite`, `theory.finite_criterion_dp`,
`theory.verify_support_bound`, `theory.verify_support_bound_dp`,
`theory.verify_R15_finite`) —
different coordinates and algorithms, with agreeing results.

## Roadmap (not yet formalized)

- Lemma S past R = 31: the verified-DP machinery of `LemmaS31.lean`
  extends directly (R = 43, 47, …); the cost is the evaluator's DP
  run, which grows with the state count (3,001 at R = 31; millions by
  R = 83), eventually needing a compacter state representation. Note,
  though, that Theorem 1.10(i) is now formalized
  (`theoremS_support_bound`) and proves the support bound for every
  even d at once, so DP extensions past R = 31 would be independent
  confirmations only.
- Near-term plan: the ladder Lemmas J° and N plus the
  selected-residual corollary are **done** (`Ladder.lean`:
  `composite_reciprocity`, `jacobi_necessity`,
  `selected_residual_nonresidue`, standard axioms only); the R = 15
  product-index mask bridge is **done** (`BridgeR15.lean`:
  `theoremA'''_finite_R15` / `_mult`, the paper's Theorem 1.6); the
  Kneser port for Theorem 1.10(i) is **done** (`Kneser/` vendored +
  `TheoremS.lean`, standard axioms only), as is its odd-modulus
  variant (`theoremS_support_bound_odd`); the kernel branch of the
  branch classification (Theorem 4.8) and β-vacuity
  (Proposition 4.12) are **done** (`KernelBranch.lean`, standard
  axioms only); remaining from that list:
  Theorem 1.10(ii) (the general-abelian composite form with the
  involution correction), and connecting `theoremS_support_bound` to
  the `reach` model in the way `lemmaS_finite_R19_mult` is connected
  (a discrete-log instantiation of `M(S)`).
- The **iterated** Reduction Lemma of Theorem 4.8 (strong induction on
  `d`: compose the single kernel-branch step of `kernel_branch` into a
  chain of quotients down to an aperiodic maximal failing support
  `T′`, so that every failing support lies in `ψ⁻¹({0} ∪ T′) \ {0}`
  for a composed quotient `ψ`). The single step, including the size
  bookkeeping `(h−1) + h·#T̄ ≤ d/2 − 1`, is formalized; the
  composition — which additionally needs "extend `T̄` to a maximal
  support downstairs" — is not.
- Theorem 4.7's count (`2^{c√d}` maximal failing supports): the
  complete-partition mechanism is formalized
  (`sums2_of_completePartition`, `completePartition_failing`), the
  counting of the family (distinctness of the `2^{c√d}` supports) is
  not.
- Conjecture A (the aperiodic branch classification) and the
  conditional Theorems 4.10 / 4.11 that rest on it: out of scope —
  what `KernelBranch.lean` contributes is the *unconditional* half
  (the kernel branch) plus the proof that the punctured failure mode
  is vacuous.
- Composed corollaries at R = 11, 23, 31 analogous to
  `lemmaS_R19_certificate` (same recipe).
- The analytic sieve bounds (the chain of Theorem 1.11, the density
  reduction, and the §5 analytic ladder theorems B₁/B₂/P₁/L₁) and the
  large-scale computations of the paper's §6 are out
  of scope by design (see the paper's trusted-computing-base
  discussion): they remain independently reproducible software with
  deterministic verification.

## Modules

| File | Contents |
|---|---|
| `ErdosStraus.lean` | import root: pulls in the modules below in dependency order |
| `Basic.lean` | certificate soundness/integrality, Theorem J (reciprocity) |
| `Families.lean` | the aggregate identity families (Proposition 1.12), hard-class lemmas |
| `TheoremA.lean` | Theorem A (R = 3), both directions, with positivity, for both hard-prime classes mod 3 (`theoremA_necessity` / `theoremA_sufficiency` at p ≡ 1, `theoremA_two_mod_three` at p ≡ 2) |
| `Ladder.lean` | the Burgess–reciprocity ladder's elementary layer: Lemma J° (composite reciprocity), Lemma N (Jacobi necessity), the selected-residual corollary |
| `Enumerations.lean` | the `reach` model, the monotonicity lemmas, the cap-saturation chain making the multiplicity cap lossless (`powers_saturate` … `reach_mult_cap`), and the four `native_decide` finite checks (R = 7, 11, 19, 23) |
| `Bridges.lean` | the parametric discrete-log bridge and the three `_mult` multiplicative restatements |
| `BridgeR15.lean` | the product-index mask bridge for non-cyclic unit groups and Theorem A‴ (R = 15, paper Theorem 1.6): finite check + multiplicative restatement |
| `DivisorBridge.lean` | reach ⟺ divisor certificates (FTA), budget consolidation, the composed corollary |
| `LemmaS31.lean` | Lemma S at R = 31 by certified dynamic programming |
| `Kneser/MulStab.lean`, `Kneser/Kneser.lean` | Kneser's addition theorem and the finset-stabilizer API, **vendored unmodified** from [Yaël Dillies' misc-yd](https://github.com/YaelDillies/misc-yd) (Apache 2.0; commit and provenance in the file headers) |
| `TheoremS.lean` | iterated Kneser (`add_kneser_list`) and Theorem S — the paper's Theorem 1.10(i), the unconditional support bound — plus its odd-modulus variant `theoremS_support_bound_odd` |
| `KernelBranch.lean` | the kernel branch of the branch classification (the paper's Theorem 4.8: lossless reduction along `φ_H`, maximality, the container and its size bookkeeping), β-vacuity (Proposition 4.12), and the complete-partition lemma behind Theorem 4.7 |

## Build

```bash
cd lean/ErdosStraus
lake exe cache get   # fetch mathlib binaries
lake build           # ~minutes after cache; audits axioms via #print
```
