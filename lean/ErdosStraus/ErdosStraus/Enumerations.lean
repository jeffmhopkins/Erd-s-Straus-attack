/-
The finite-enumeration layer: a computable model of divisor-class
reachability (the content of the meta-theorem's reduction), the two
monotonicity lemmas that drive it, and the finite checks behind
Theorem A′ (R = 7), Theorem A″ (R = 11), and Lemma S at R = 19 and 23.

Model. A configuration is a list of pairs `(x, b) : ZMod R × ℕ`: a
factor class `x` of `m = p·a` together with an exponent budget `b`
(twice the multiplicity, capped — exponents only matter modulo the
order of `x`). `reach l` is the set of classes of divisors `k ∣ m²`
realizable within the budgets; residual `R` succeeds at `p` iff the
target class `−m = −4⁻¹p²` lies in `reach`.

The four finite theorems at the bottom mirror, statement for
statement, the Python verifiers `theory.verify_R7_finite` (1,536
consistent configurations; stated multiplicatively over `ZMod 7`),
`theory.finite_criterion_dp` at R = 11, and
`theory.verify_support_bound` at R = 19 and 23 — the latter three in
the discrete-log coordinates of their proofs (see the docstring of
`lemmaS_finite_R19` for why). All are discharged by `native_decide`;
see lean/README.md for the trust base, and `Bridges.lean` for the
proved translations back to the multiplicative model.
-/
import Mathlib.Tactic

namespace ErdosStraus

open Finset

variable {R : ℕ}

/-- Powers `x^e` for `e ≤ b`. -/
def powers (x : ZMod R) (b : ℕ) : Finset (ZMod R) :=
  (range (b + 1)).image (x ^ ·)

/-- One step of the reachability fold: multiply every element of `S`
by every allowed power of `xb.1`. -/
def step (S : Finset (ZMod R)) (xb : ZMod R × ℕ) : Finset (ZMod R) :=
  S.biUnion fun s => (powers xb.1 xb.2).image (s * ·)

/-- Reachable divisor classes from a list of (class, exponent-budget)
pairs. -/
def reach (l : List (ZMod R × ℕ)) : Finset (ZMod R) :=
  l.foldl step {1}

lemma one_mem_powers (x : ZMod R) (b : ℕ) : (1 : ZMod R) ∈ powers x b := by
  simp only [powers, mem_image]
  exact ⟨0, by simp, by simp⟩

lemma powers_mono (x : ZMod R) {b b' : ℕ} (h : b ≤ b') :
    powers x b ⊆ powers x b' := by
  intro z hz
  simp only [powers, mem_image, mem_range] at hz ⊢
  obtain ⟨e, he, rfl⟩ := hz
  exact ⟨e, by omega, rfl⟩

lemma step_mono {S S' : Finset (ZMod R)} (hS : S ⊆ S')
    {xb xb' : ZMod R × ℕ} (hx : xb.1 = xb'.1) (hb : xb.2 ≤ xb'.2) :
    step S xb ⊆ step S' xb' := by
  have hpow : powers xb.1 xb.2 ⊆ powers xb'.1 xb'.2 := by
    rw [← hx]; exact powers_mono _ hb
  intro z hz
  simp only [step, mem_biUnion, mem_image] at hz ⊢
  obtain ⟨s, hs, w, hw, rfl⟩ := hz
  exact ⟨s, hS hs, w, hpow hw, rfl⟩

lemma subset_step (S : Finset (ZMod R)) (xb : ZMod R × ℕ) :
    S ⊆ step S xb := by
  intro s hs
  simp only [step, mem_biUnion, mem_image]
  exact ⟨s, hs, 1, one_mem_powers _ _, mul_one s⟩

/-- **Monotonicity in budgets** (the formal core of the meta-theorem's
reduction): enlarging exponent budgets entrywise can only enlarge the
reachable set. -/
lemma reach_mono {l l' : List (ZMod R × ℕ)}
    (h : List.Forall₂ (fun ab ab' => ab.1 = ab'.1 ∧ ab.2 ≤ ab'.2) l l') :
    reach l ⊆ reach l' := by
  suffices key : ∀ {S S' : Finset (ZMod R)}, S ⊆ S' →
      l.foldl step S ⊆ l'.foldl step S' by exact key subset_rfl
  induction h with
  | nil =>
      intro S S' hS
      simpa using hS
  | cons hab _ ih =>
      intro S S' hS
      simp only [List.foldl_cons]
      exact ih (step_mono hS hab.1 hab.2)

/-- **Monotonicity in support** (the reduction behind Lemma S's
multiplicity-1 check): dropping factor classes can only shrink the
reachable set. -/
lemma reach_sublist {l l' : List (ZMod R × ℕ)} (h : List.Sublist l l') :
    reach l ⊆ reach l' := by
  suffices key : ∀ {S S' : Finset (ZMod R)}, S ⊆ S' →
      l.foldl step S ⊆ l'.foldl step S' by exact key subset_rfl
  induction h with
  | slnil =>
      intro S S' hS
      simpa using hS
  | cons xb _ ih =>
      intro S S' hS
      simp only [List.foldl_cons]
      exact ih (hS.trans (subset_step S' xb))
  | cons_cons xb _ ih =>
      intro S S' hS
      simp only [List.foldl_cons]
      exact ih (step_mono hS rfl le_rfl)

/-! ### Finite checks

Concrete instances of the meta-theorem's enumeration. Conventions
shared with the Python verifiers:

* `c i` is the multiplicity of the class `i` among the prime factors
  of `a = (p+R)/4`; each class enters divisors of `m² = (pa)²` with
  exponent at most `2·(c i)`; `p` itself has exponent budget `2`.
* Hard primes force `p` to be a QR mod `R` and (mod 8) force the
  class 2 to appear in `a`; consistency forces
  `∏ classes^mult = a ≡ 4⁻¹·p (mod R)`.
* The target class is `−m ≡ −4⁻¹·p² (mod R)`.
-/

/-- **Theorem A′, finite verification (R = 7).** `cᵢ` is the (capped)
multiplicity of the unit class `i` among the prime factors of
`a = (p+7)/4`. For every consistent hard-prime configuration
(multiplicities capped at 3 = ⌈(R−1)/2⌉, class 2 present, `p` a QR,
`∏ classes = a ≡ 4⁻¹p = 2p`), the target `−m = −2p² = 5p²` is
reachable **iff** some present class is a quadratic non-residue mod 7
(one of `3, 5, 6`). The neutral class 1 is omitted: its powers are all
1, which the model already contains — the 1,536 consistent
configurations of `theory.verify_R7_finite` collapse to the 384
checked here (four values of the neutral multiplicity each). -/
theorem theoremA'_finite_R7 :
    ∀ (c2 c3 c4 c5 c6 : Fin 4) (p : ZMod 7),
      c2 ≠ 0 →
      (p = 1 ∨ p = 2 ∨ p = 4) →
      (2 : ZMod 7) ^ c2.val * 3 ^ c3.val * 4 ^ c4.val * 5 ^ c5.val *
          6 ^ c6.val = 2 * p →
      (5 * p ^ 2 ∈
          reach [((2 : ZMod 7), 2 * c2.val), (3, 2 * c3.val),
            (4, 2 * c4.val), (5, 2 * c5.val), (6, 2 * c6.val), (p, 2)]
        ↔ (c3 ≠ 0 ∨ c5 ≠ 0 ∨ c6 ≠ 0)) := by
  native_decide

/-- Cyclic rotation of an 18-bit mask: the action of "multiply by
`g^s`" on subsets of `(ℤ/19)ˣ` written in discrete-log coordinates
(primitive root `g = 2`; bit `i` stands for the class `2^i mod 19`). -/
def rot18 (m s : ℕ) : ℕ :=
  ((m <<< (s % 18)) ||| (m >>> (18 - s % 18))) &&& (2 ^ 18 - 1)

/-- **Lemma S, finite verification at R = 19**, in the discrete-log
coordinates of its proof (and of `theory.verify_support_bound`): bit
`i` of a mask is the class `2^i mod 19`, so a factor class of log `v`
with exponent budget 2 contributes rotations by `0, v, 2v`, and `p`
(log `plog`) contributes rotations by `0, plog, 2·plog`. The target
`−4⁻¹p²` has log `(9 + 2·plog + 16) % 18 = (2·plog + 7) % 18` (since
`log 2 (−1) = 9` and `log 2 (4⁻¹) = log 2 5 = 16`).

Claim: every support of 9 nonzero logs reaches the target already at
multiplicity 1, for every class of `p` — all C(17,9) = 24,310 supports
× 18 classes = 437,580 checks. By the monotonicity of reachability in
support and multiplicities (`reach_mono` / `reach_sublist` in the
multiplicative model), failing configurations therefore occupy at most
8 nonzero classes: the support bound. The discrete-log translation
back to the multiplicative model is proved in `Bridges.lean`
(`maskSet_rotg`, `reach_eq_maskSet`) and applied there to derive the
multiplicative form `lemmaS_finite_R19_mult`; the mask coordinates
are used here only because the `Finset`-over-`ZMod` evaluation is
impractical for `native_decide` at R = 19. -/
theorem lemmaS_finite_R19 :
    ∀ S ∈ Finset.powersetCard 9 (Finset.Icc 1 17),
      ∀ plog : ℕ, plog < 18 →
        (let base := (List.range 18).foldl
            (fun b v => if v ∈ S then b ||| rot18 b v ||| rot18 b (2 * v)
             else b) 1
         Nat.testBit (base ||| rot18 base plog ||| rot18 base (2 * plog))
           ((2 * plog + 7) % 18)) = true := by
  native_decide

/-- Cyclic rotation of a 10-bit mask: discrete-log coordinates for
`(ℤ/11)ˣ` (primitive root `g = 2`; bit `i` is the class `2^i mod 11`). -/
def rot10 (m s : ℕ) : ℕ :=
  ((m <<< (s % 10)) ||| (m >>> (10 - s % 10))) &&& (2 ^ 10 - 1)

/-- **Theorem A″, finite verification (R = 11)**, in discrete-log
coordinates (primitive root 2). Class↔log dictionary:
`2↦1, 3↦8, 4↦2, 5↦4, 6↦9, 7↦7, 8↦3, 9↦6, 10↦5`; quadratic residues
are the even logs. `mᵥ` is the (capped) multiplicity of the class of
log `v` among the prime factors of `a = (p+11)/4`; caps are by order
(`ord(g^v) = 10/gcd(v,10)`): logs `1,3,7,9` cap 5, logs `2,4,6,8`
cap 3, log `5` cap 1 — a budget of twice the cap covers the full
cyclic subgroup, so higher multiplicities are model-equivalent. The
neutral log 0 is omitted.

Structure at hard primes: `3 ∣ a` forces the class 3 (log 8), so
`m₈ ≥ 1`; consistency determines `p`:
`plog = (Σ v·mᵥ + 2) % 10` (since `log 4⁻¹ = log 3 = 8`), and the
target `−m` has log `(5 + alog + plog) % 10` (`log(−1) = 5`).

Claim (the exact criterion): the target is reachable **iff** the
configuration is *not* of the two failure shapes of Theorem A″ —
(a) all factor classes are quadratic residues (all odd logs absent),
or (b) `v₃(a) = 1`, every other class trivial except a non-residue
part `{class 2}`, `{class 6}`, or `{class 2, class 6}` at
multiplicity one (logs 1 and 9), paired with `p ≡ 2, 6, 1 (mod 11)`
respectively. All 497,664 consistent capped configurations. -/
theorem theoremA''_finite_R11 :
    ∀ (m1 m3 m7 m9 : Fin 6) (m2 m4 m6 m8 : Fin 4) (m5 : Fin 2),
      1 ≤ m8.val →
      (let alog := (m1.val + 2 * m2.val + 3 * m3.val + 4 * m4.val +
          5 * m5.val + 6 * m6.val + 7 * m7.val + 8 * m8.val +
          9 * m9.val) % 10
       let plog := (alog + 2) % 10
       let base := [(1, m1.val), (2, m2.val), (3, m3.val), (4, m4.val),
          (5, m5.val), (6, m6.val), (7, m7.val), (8, m8.val),
          (9, m9.val)].foldl
           (fun b vm => if vm.2 = 0 then b else
             (List.range (2 * vm.2 + 1)).foldl
               (fun acc e => acc ||| rot10 b (vm.1 * e)) 0) 1
       (Nat.testBit (base ||| rot10 base plog ||| rot10 base (2 * plog))
           ((5 + alog + plog) % 10)
         == !(((m1 == 0) && (m3 == 0) && (m5 == 0) && (m7 == 0) &&
                (m9 == 0)) ||
              ((m8 == 1) && (m2 == 0) && (m4 == 0) && (m6 == 0) &&
                (m3 == 0) && (m5 == 0) && (m7 == 0) &&
                (((m1 == 1) && (m9 == 0) && (plog == 1)) ||
                 ((m1 == 0) && (m9 == 1) && (plog == 9)) ||
                 ((m1 == 1) && (m9 == 1) && (plog == 0)))))) = true) := by
  native_decide

/-- Cyclic rotation of a 22-bit mask: discrete-log coordinates for
`(ℤ/23)ˣ` (primitive root `g = 5`; bit `i` is the class `5^i mod 23`). -/
def rot22 (m s : ℕ) : ℕ :=
  ((m <<< (s % 22)) ||| (m >>> (22 - s % 22))) &&& (2 ^ 22 - 1)

/-- **Lemma S, finite verification at R = 23**, exactly parallel to
`lemmaS_finite_R19` (primitive root 5; the target `−4⁻¹p²` has log
`(11 + 2·plog + 18) % 22 = (2·plog + 7) % 22`, since `log₅(−1) = 11`
and `log₅(4⁻¹) = log₅ 6 = 18`). Every support of (23−1)/2 = 11
nonzero logs reaches the target at multiplicity 1 for every class of
`p`: C(21,11) = 352,716 supports × 22 classes = 7,759,752 checks —
failing configurations occupy at most 10 nonzero classes. The inner
quantifier over `p` is phrased with `List.all` so the evaluator
computes each support's base mask once. -/
theorem lemmaS_finite_R23 :
    ∀ S ∈ Finset.powersetCard 11 (Finset.Icc 1 21),
      ((let base := (List.range 22).foldl
            (fun b v => if v ∈ S then b ||| rot22 b v ||| rot22 b (2 * v)
             else b) 1
        (List.range 22).all fun plog =>
          Nat.testBit (base ||| rot22 base plog ||| rot22 base (2 * plog))
            ((2 * plog + 7) % 22)) = true) := by
  native_decide

end ErdosStraus

-- Audit. The monotonicity lemmas must report only the standard axioms;
-- the finite checks additionally report a per-theorem
-- `..._native.native_decide.ax_1_1` axiom, the `Lean.ofReduceBool` mechanism (trust
-- in the compiled evaluator — kernel reduction of Finset/Multiset
-- computations is impractical at this scale; every enumeration is
-- independently cross-checked by the Python implementations. See
-- lean/README.md).
#print axioms ErdosStraus.reach_mono
#print axioms ErdosStraus.reach_sublist
#print axioms ErdosStraus.theoremA'_finite_R7
#print axioms ErdosStraus.lemmaS_finite_R19
#print axioms ErdosStraus.theoremA''_finite_R11
#print axioms ErdosStraus.lemmaS_finite_R23
