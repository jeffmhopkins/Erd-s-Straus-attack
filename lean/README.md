# Lean formalization

Machine-checked (Lean 4.32.2 + mathlib) formalization of the core
residual framework from the companion paper.

## Verified (sorry-free; audited by `#print axioms`)

| Declaration | Paper counterpart |
|---|---|
| `certificate_sound` | §1.1: a factorization k·k′ = m² with R·b = k+m, R·c = k′+m yields the Erdős–Straus identity 4abc = p(bc+ac+ab) |
| `certificate_integrality` | §1.1: R ∣ k+m and gcd(R,k)=1 force R ∣ k′+m, so b, c are integers |
| `reciprocity_structure` | Theorem J: (q\|R) = (p\|q) for odd primes q ≠ R with R ≡ 3 (mod 4), q ∣ p+R |
| `theoremA_necessity` | Theorem A (⇒): all prime factors of a ≡ 1 (mod 3) blocks every divisor k of (pa)² from the class −pa (mod 3) |
| `theoremA_sufficiency` | Theorem A (⇐): a divisor q ≡ 2 (mod 3) of a yields positive b, c with the identity (k = q) |
| `divisor_one_mod_three` | the multiplicative-closure lemma behind necessity |
| `family_p_plus_one` | Theorem I: R ∣ p+1 certifies via k = a·p² |
| `family_p_plus_four` | Theorem I: R ∣ p+4 (R odd) certifies via k = a²·p |
| `hard_classes_are_squares` | the six Mordell classes are squares of units mod 840 (explicit witnesses 1², 11², 13², 17², 19², 23²) |
| `hard_classes_local` | Corollary J1's arithmetic core: hard classes ≡ 1 (mod 8), ≡ 1 (mod 3), QR mod 5 and mod 7 |
| `reach` / `powers` / `step` | the meta-theorem's finite model: divisor-class reachability from (class, exponent-budget) pairs, computably, in ZMod R |
| `reach_mono` | Lemma 3.2 (monotonicity reduction), budget half: entrywise larger exponent budgets enlarge the reachable set |
| `reach_sublist` | Lemma 3.2, support half: dropping factor classes shrinks the reachable set |
| `theoremA'_finite_R7` | Theorem A′'s finite verification: all 1,536 consistent hard-prime configurations at R = 7 (384 after collapsing the neutral class), stated in the multiplicative `reach` model — target −m reachable ⟺ a non-residue class is present (`native_decide`) |
| `rot18` / `lemmaS_finite_R19` | Lemma S at R = 19: every 9-class support reaches the target at minimal multiplicities, for every class of p — C(17,9) = 24,310 supports × 18 = 437,580 checks, stated in the discrete-log coordinates of the proof (`native_decide`) |
| `rot10` / `theoremA''_finite_R11` | Theorem A″'s finite verification: all 497,664 consistent capped configurations at R = 11 — target reachable ⟺ neither failure shape (all-QR, or the three exact budget patterns), in discrete-log coordinates (`native_decide`) |
| `rot22` / `lemmaS_finite_R23` | Lemma S at R = 23: C(21,11) = 352,716 supports × 22 = 7,759,752 checks, same form as R = 19 (`native_decide`) |
| `rotg` / `maskSet` / `mstep` (Bridges.lean) | the parametric discrete-log bridge: a mask represents a set of classes, rotation is multiplication by g^s (`maskSet_rotg`), the mask fold is `reach` (`maskSet_mstep`, `reach_eq_maskSet`) — standard axioms only |
| `reach_perm` / `reach_append_single` | `reach` is invariant under permutations of the configuration list (step is right-commutative) |
| `lemmaS_finite_R19_mult` / `lemmaS_finite_R23_mult` | the support bounds **restated over `ZMod 19` / `ZMod 23` and the multiplicative `reach` model** (any duplicate-free enumeration of any 9- resp. 11-class support), derived from the mask checks via the bridge |
| `theoremA''_finite_R11_mult` | Theorem A″'s exact criterion **restated over `ZMod 11`** — class-indexed multiplicities, consistency-determined p, reach membership ⟺ neither failure shape — derived via the bridge |

Together these verify the elementary layer of the paper end to end —
certificates are sound and integral, Theorem A is exact in both
directions, both aggregate identity families certify, the reciprocity
identity governing joint failure is correct, and the hard-class local
structure is checked — plus the finite-enumeration layer: the
meta-theorem's reachability model with both monotonicity reductions,
the R = 7 check stated directly in that multiplicative model
(`ZMod 7`, no discrete-log encoding), the full R = 11 criterion
(Theorem A″'s exact two-case failure classification), and the
R = 19 and R = 23 support-bound checks — the latter three evaluated
in the discrete-log coordinates their proofs use, **and then carried
back to the multiplicative model by the formally proved discrete-log
bridges** (`Bridges.lean`): the mask semantics (rotation =
multiplication by `g^s`, mask fold = `reach`) is a theorem, so
`theoremA''_finite_R11_mult`, `lemmaS_finite_R19_mult`, and
`lemmaS_finite_R23_mult` state the same results directly over
`ZMod 11 / 19 / 23` and `reach`, with no coordinate caveat left.

### Trust base

Every declaration is audited by `#print axioms`. The model and the
monotonicity lemmas report only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). The four finite checks use
`native_decide` and so additionally report a `…native_decide.ax_1_1`
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
enumeration's single `native_decide` axiom and nothing else.
Mitigation for the evaluator trust: every enumeration is checked by
independent Python implementations (`theory.verify_R7_finite`,
`theory.finite_criterion_dp`, `theory.verify_support_bound`) written
against the same finite spaces, with identical results.

## Roadmap (not yet formalized)

- Lemma S past R = 23: C(25,13) × 26 ≈ 135M checks at R = 31 exceeds
  the evaluator's practical budget; the DP formulation (or a
  precompiled checker) would be needed.
- The bridge theorems connecting `reach` to actual divisor
  certificates (the meta-theorem's reduction itself, currently proved
  in the paper): `reach` membership ⟺ ∃ k ∣ m² in the target class.
- The sieve chapter is out of scope by design (see the paper's
  trusted-computing-base paragraph): the large-scale computations remain
  independently reproducible software with deterministic verification.

## Build

```
cd lean/ErdosStraus
lake exe cache get   # fetch mathlib binaries
lake build           # ~seconds after cache; audits axioms via #print
```
