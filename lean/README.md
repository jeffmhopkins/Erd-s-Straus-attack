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
| `theoremA_necessity` | Theorem A (⇒): all prime factors of a ≡ 1 (mod 3) blocks every divisor k of (pa)² from the class −pa (mod 3) (Lean statement assumes the hard-prime congruence p ≡ 1 (mod 3); the paper's Theorem 1.2 covers all 3 ∤ p) |
| `theoremA_sufficiency` | Theorem A (⇐): a divisor q ≡ 2 (mod 3) of a yields positive b, c with the identity (k = q) (same hard-prime congruence assumption as necessity) |
| `divisor_one_mod_three` | the multiplicative-closure lemma behind necessity |
| `composite_reciprocity` | Lemma 5.1 (Lemma J°): (q\|R) = (p\|q) with the left symbol Jacobi, for any R ≡ 3 (mod 4) — prime or composite — and odd prime q ∣ p+R (the paper's gcd(q,R)=1 hypothesis turns out unnecessary) |
| `jacobi_necessity` / `divisor_jacobiSym_one` | Lemma 5.2 (Lemma N): if every prime factor of a has Jacobi symbol +1 mod R, no divisor k of (pa)² lies in the class −pa (mod R) — via the Jacobi analogue of the multiplicative-closure lemma |
| `selected_residual_nonresidue` | selected residual, §5.1: with (p\|q) = −1 and 4q ∣ p+R (as at R₀ = (−p) mod 4q and every ladder rung), (q\|R) = −1 — the all-residue failure mode of Lemma N is impossible at R by construction |
| `family_p_plus_one` | Proposition 1.12 (Theorem I in the notes): R ∣ p+1 certifies via k = a·p² (identity and integrality; positivity of b, c not part of the statement) |
| `family_p_plus_four` | Proposition 1.12: R ∣ p+4 (R odd) certifies via k = a²·p (identity and integrality; positivity of b, c not part of the statement) |
| `hard_classes_are_squares` | the six Mordell classes are squares of units mod 840 (explicit witnesses 1², 11², 13², 17², 19², 23²) |
| `hard_classes_local` | Corollary 2.3(i)'s arithmetic core: hard classes ≡ 1 (mod 8), ≡ 1 (mod 3), QR mod 5 and mod 7 |
| `reach` / `powers` / `step` | the meta-theorem's finite model: divisor-class reachability from (class, exponent-budget) pairs, computably, in ZMod R |
| `reach_mono` | Lemma 4.1 (monotonicity reduction), budget half: entrywise larger exponent budgets enlarge the reachable set |
| `reach_sublist` | Lemma 4.1, support half: dropping factor classes shrinks the reachable set |
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

Together these verify the elementary layer of the paper end to end —
certificates are sound and integral, Theorem A is exact in both
directions (as stated under the hard-prime congruence p ≡ 1 (mod 3);
the paper's Theorem 1.2 covers all 3 ∤ p), both aggregate identity
families certify (identity + integrality; positivity unchecked), the
reciprocity
identity governing joint failure is correct — including its composite
form and the ladder's elementary layer (Lemmas 5.1, 5.2 and the
selected-residual corollary, `Ladder.lean`) — and the hard-class local
structure is checked — plus the finite-enumeration layer: the
meta-theorem's reachability model with both monotonicity reductions,
the R = 7 check stated directly in that multiplicative model
(`ZMod 7`, no discrete-log encoding), the full (capped) R = 11
criterion
(Theorem A″'s exact two-case failure classification), and the
R = 19 and R = 23 support-bound checks — the latter three evaluated
in the discrete-log coordinates their proofs use, **and then carried
back to the multiplicative model by the formally proved discrete-log
bridges** (`Bridges.lean`): the mask semantics (rotation =
multiplication by `g^s`, mask fold = `reach`) is a theorem, so
`theoremA''_finite_R11_mult`, `lemmaS_finite_R19_mult`, and
`lemmaS_finite_R23_mult` state the same results directly over
`ZMod 11 / 19 / 23` and `reach`, with no coordinate caveat left.
Finally, the reach ⟺ divisor-certificate bridge
(`DivisorBridge.lean`) proves the model faithful to the integers:
`reach` membership of a class is existence of a divisor of `m²` in
that class (via the fundamental theorem of arithmetic), and reach
membership of the target `−m` produces an explicit positive
Erdős–Straus certificate (`reach_certificate`) — the meta-theorem's
reduction itself, fully symbolic, standard axioms only.

### Trust base

Every main theorem is audited by `#print axioms` (40 audit lines;
helper lemmas are covered transitively through the audited theorems). The model and the
monotonicity lemmas report only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). The five finite checks (four enumerations plus the R = 31
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
`theory.verify_support_bound`, `theory.verify_support_bound_dp`) —
different coordinates and algorithms, with agreeing results.

## Roadmap (not yet formalized)

- Lemma S past R = 31: the verified-DP machinery of `LemmaS31.lean`
  extends directly (R = 43, 47, …); the cost is the evaluator's DP
  run, which grows with the state count (3,001 at R = 31; millions by
  R = 83), eventually needing a compacter state representation. Note,
  though, that Theorem 1.10 (Kneser) now proves the support bound for
  every R, so DP extensions past R = 31 would be independent
  confirmations only; the real unformalized targets are Theorem 1.10
  itself and Theorem 1.6 (R = 15).
- Near-term plan: the ladder Lemmas J° and N plus the
  selected-residual corollary are **done** (`Ladder.lean`:
  `composite_reciprocity`, `jacobi_necessity`,
  `selected_residual_nonresidue`, standard axioms only); remaining:
  an R = 15 product-index mask bridge, and a Kneser port for
  Theorem 1.10(i)(ii).
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
| `TheoremA.lean` | Theorem A (R = 3), both directions, with positivity |
| `Ladder.lean` | the Burgess–reciprocity ladder's elementary layer: Lemma J° (composite reciprocity), Lemma N (Jacobi necessity), the selected-residual corollary |
| `Enumerations.lean` | the `reach` model, monotonicity lemmas, and the four `native_decide` finite checks (R = 7, 11, 19, 23) |
| `Bridges.lean` | the parametric discrete-log bridge and the three `_mult` multiplicative restatements |
| `DivisorBridge.lean` | reach ⟺ divisor certificates (FTA), budget consolidation, the composed corollary |
| `LemmaS31.lean` | Lemma S at R = 31 by certified dynamic programming |

## Build

```bash
cd lean/ErdosStraus
lake exe cache get   # fetch mathlib binaries
lake build           # ~minutes after cache; audits axioms via #print
```
