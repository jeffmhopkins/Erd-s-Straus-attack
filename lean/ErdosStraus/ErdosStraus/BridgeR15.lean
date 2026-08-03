/-
The R = 15 product-index bridge: Theorem A‴ (the paper's Theorem 1.6),
finite verification and multiplicative restatement.

The unit group `(ℤ/15)ˣ ≅ ℤ/2 × ℤ/4` is *not* cyclic, so the
discrete-log mask machinery of `Bridges.lean` (a single cyclic
rotation) does not apply. This file builds the product-index analogue:
masks over `Fin d1 × Fin d2` flattened to `d1·d2`-bit naturals (bit
`i·d2 + j` stands for the class `g^i · h^j`), rotation is componentwise
block rotation (`rot2`), and the accumulate-rotations step (`mstep2`)
represents the divisor-class `step` — the analogues of `maskSet_rotg`,
`maskSet_mstep`, and `reach_eq_maskSet`, proved symbolically for any
`R`, `d1`, `d2`, `g`, `h` with `g ^ d1 = 1` and `h ^ d2 = 1`.

At R = 15 the coordinates are `(ℤ/15)* = ⟨11⟩ × ⟨7⟩` (11 ↦ (1,0) has
order 2, 7 ↦ (0,1) has order 4): the dictionary is
`1 ↦ (0,0), 7 ↦ (0,1), 4 ↦ (0,2), 13 ↦ (0,3), 11 ↦ (1,0), 2 ↦ (1,1),
14 ↦ (1,2), 8 ↦ (1,3)`; the Jacobi non-residues mod 15 are the classes
with odd coordinate sum, `{7, 11, 13, 14}`.

`theoremA'''_finite_R15` is the finite verification of the paper's
Theorem 1.6, mirroring `theory.verify_R15_finite`: over all
consistent hard-prime configurations — multiplicities `0..5` per unit
class, the class 2 forced (`8 ∣ p+15`), `p mod 15 ∈ {1, 4}`,
consistency `∏ classes = a ≡ 4p (mod 15)`; 349,920 configurations in
all — the target `−m ≡ 11 (mod 15)` is reachable **iff** some factor
class has Jacobi symbol −1 mod 15. In contrast to R = 11 there are no
budget failure shapes at all: the criterion is a pure character
dichotomy (349,380 successes, 540 all-residue failures). Discharged by
`native_decide` in mask coordinates; `theoremA'''_finite_R15_mult`
carries it back to `ZMod 15` and the multiplicative `reach` model
through the proved product bridge, adding no computational trust.
-/
import ErdosStraus.Bridges

namespace ErdosStraus

open Finset

/-! ### Bit-fold helper -/

/-- Bits of an accumulate-single-bits fold: bit `n` of the result is
bit `n` of the accumulator, or else some listed `k` passes the guard
and maps to `n`. -/
lemma testBit_or_shift_foldl (P : ℕ → Bool) (f : ℕ → ℕ) :
    ∀ (L : List ℕ) (A n : ℕ),
      (L.foldl (fun acc k => if P k then acc ||| 1 <<< f k else acc)
          A).testBit n
        = (A.testBit n || L.any fun k => P k && decide (f k = n))
  | [], A, n => by simp
  | k :: L, A, n => by
      simp only [List.foldl_cons, List.any_cons]
      rw [testBit_or_shift_foldl P f L _ n]
      by_cases hk : P k = true
      · rw [if_pos hk, hk, Nat.testBit_or, Nat.one_shiftLeft,
          Nat.testBit_two_pow, Bool.true_and, Bool.or_assoc]
      · rw [if_neg hk]
        rw [Bool.not_eq_true] at hk
        rw [hk, Bool.false_and, Bool.false_or]

/-! ### Parametric product-index mask layer

Masks over the product index `Fin d1 × Fin d2`, flattened: bit
`i·d2 + j` stands for the unit class `g^i · h^j`. Everything is
parametric in `R`, `d1`, `d2`, `g`, `h`; the only inputs used by the
semantics lemmas are `g ^ d1 = 1`, `h ^ d2 = 1`, and positivity. -/

section ProductMask

variable {R : ℕ} (d1 d2 : ℕ) (g h : ZMod R)

/-- Product-index block rotation of a `d1·d2`-bit mask: the bit at
`(i, j)` moves to `((i+s) mod d1, (j+t) mod d2)` — the action of
"multiply by `g^s · h^t`" on subsets of the product group. -/
def rot2 (M s t : ℕ) : ℕ :=
  (List.range (d1 * d2)).foldl
    (fun acc k =>
      if M.testBit k then
        acc ||| 1 <<< ((k / d2 + s) % d1 * d2 + (k % d2 + t) % d2)
      else acc) 0

lemma testBit_rot2 (M s t n : ℕ) :
    (rot2 d1 d2 M s t).testBit n =
      ((List.range (d1 * d2)).any fun k => M.testBit k &&
        decide ((k / d2 + s) % d1 * d2 + (k % d2 + t) % d2 = n)) := by
  have hfold := testBit_or_shift_foldl (fun k => M.testBit k)
    (fun k => (k / d2 + s) % d1 * d2 + (k % d2 + t) % d2)
    (List.range (d1 * d2)) 0 n
  simp only [Nat.zero_testBit, Bool.false_or] at hfold
  exact hfold

/-- Flattened product indices stay below `d1·d2`. -/
lemma idx_lt {i j : ℕ} (hi : i < d1) (hj : j < d2) :
    i * d2 + j < d1 * d2 :=
  calc i * d2 + j < i * d2 + d2 := by omega
    _ = (i + 1) * d2 := by ring
    _ ≤ d1 * d2 := Nat.mul_le_mul hi le_rfl

lemma idx_div {i j : ℕ} (hd2 : 0 < d2) (hj : j < d2) :
    (i * d2 + j) / d2 = i := by
  rw [Nat.mul_comm i d2, Nat.mul_add_div hd2, Nat.div_eq_of_lt hj,
    Nat.add_zero]

lemma idx_mod {i j : ℕ} (hj : j < d2) : (i * d2 + j) % d2 = j := by
  rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hj]

lemma rot2_lt (hd1 : 0 < d1) (hd2 : 0 < d2) (M s t : ℕ) :
    rot2 d1 d2 M s t < 2 ^ (d1 * d2) := by
  unfold rot2
  suffices key : ∀ (L : List ℕ) (A : ℕ), A < 2 ^ (d1 * d2) →
      (L.foldl (fun acc k =>
        if M.testBit k then
          acc ||| 1 <<< ((k / d2 + s) % d1 * d2 + (k % d2 + t) % d2)
        else acc) A) < 2 ^ (d1 * d2) by
    exact key _ 0 (Nat.two_pow_pos _)
  intro L
  induction L with
  | nil => intro A hA; simpa using hA
  | cons k L ih =>
      intro A hA
      simp only [List.foldl_cons]
      apply ih
      by_cases hk : M.testBit k = true
      · rw [if_pos hk]
        refine Nat.or_lt_two_pow hA ?_
        rw [Nat.one_shiftLeft]
        exact Nat.pow_lt_pow_right (by norm_num)
          (idx_lt d1 d2 (Nat.mod_lt _ hd1) (Nat.mod_lt _ hd2))
      · rwa [if_neg hk]

/-- Rotation by `(0, 0)` is the identity on masks below `2^(d1·d2)`. -/
lemma rot2_zero (hd1 : 0 < d1) (hd2 : 0 < d2) {M : ℕ}
    (hM : M < 2 ^ (d1 * d2)) : rot2 d1 d2 M 0 0 = M := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_rot2]
  have hdest : ∀ k, k < d1 * d2 →
      ((k / d2 + 0) % d1 * d2 + (k % d2 + 0) % d2 = n ↔ k = n) := by
    intro k hk
    rw [Nat.add_zero, Nat.add_zero,
      Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul hd2).mpr hk),
      Nat.mod_eq_of_lt (Nat.mod_lt _ hd2)]
    constructor
    · intro he
      exact (Nat.div_add_mod' k d2).symm.trans he
    · rintro rfl
      exact Nat.div_add_mod' k d2
  by_cases hn : n < d1 * d2
  · cases hMn : M.testBit n with
    | true =>
        rw [List.any_eq_true]
        refine ⟨n, List.mem_range.mpr hn, ?_⟩
        rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hMn, (hdest n hn).mpr rfl⟩
    | false =>
        rw [List.any_eq_false]
        intro k hkmem
        rw [List.mem_range] at hkmem
        intro hcontra
        rw [Bool.and_eq_true, decide_eq_true_eq] at hcontra
        obtain ⟨hbit, hdk⟩ := hcontra
        rw [(hdest k hkmem).mp hdk] at hbit
        rw [hbit] at hMn
        cases hMn
  · have hMn : M.testBit n = false := by
      apply Nat.testBit_lt_two_pow
      calc M < 2 ^ (d1 * d2) := hM
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hMn, List.any_eq_false]
    intro k hkmem
    rw [List.mem_range] at hkmem
    intro hcontra
    rw [Bool.and_eq_true, decide_eq_true_eq] at hcontra
    have hlt : (k / d2 + 0) % d1 * d2 + (k % d2 + 0) % d2 < d1 * d2 :=
      idx_lt d1 d2 (Nat.mod_lt _ hd1) (Nat.mod_lt _ hd2)
    omega

/-- The set of unit classes represented by a product-index mask: bit
`i·d2 + j` stands for the class `g^i · h^j`. -/
def maskSet2 (M : ℕ) : Finset (ZMod R) :=
  ((Finset.range (d1 * d2)).filter fun k => M.testBit k).image
    fun k => g ^ (k / d2) * h ^ (k % d2)

lemma mem_maskSet2 {M : ℕ} {x : ZMod R} :
    x ∈ maskSet2 d1 d2 g h M ↔
      ∃ k, k < d1 * d2 ∧ M.testBit k ∧ g ^ (k / d2) * h ^ (k % d2) = x := by
  simp only [maskSet2, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨k, ⟨hk, hbit⟩, rfl⟩; exact ⟨k, hk, hbit, rfl⟩
  · rintro ⟨k, hk, hbit, rfl⟩; exact ⟨k, ⟨hk, hbit⟩, rfl⟩

lemma maskSet2_or (M N : ℕ) :
    maskSet2 d1 d2 g h (M ||| N) =
      maskSet2 d1 d2 g h M ∪ maskSet2 d1 d2 g h N := by
  ext x
  simp only [mem_maskSet2, mem_union, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨k, hk, hbit | hbit, rfl⟩
    · exact Or.inl ⟨k, hk, hbit, rfl⟩
    · exact Or.inr ⟨k, hk, hbit, rfl⟩
  · rintro (⟨k, hk, hbit, rfl⟩ | ⟨k, hk, hbit, rfl⟩)
    · exact ⟨k, hk, Or.inl hbit, rfl⟩
    · exact ⟨k, hk, Or.inr hbit, rfl⟩

/-- **Product rotation is multiplication by `g^s · h^t`** on
represented sets — the product-index analogue of `maskSet_rotg`. -/
lemma maskSet2_rot2 (hg1 : g ^ d1 = 1) (hh1 : h ^ d2 = 1)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (M s t : ℕ) :
    maskSet2 d1 d2 g h (rot2 d1 d2 M s t) =
      (maskSet2 d1 d2 g h M).image (· * (g ^ s * h ^ t)) := by
  ext x
  simp only [mem_maskSet2, mem_image]
  constructor
  · rintro ⟨n, hn, hbit, rfl⟩
    rw [testBit_rot2, List.any_eq_true] at hbit
    obtain ⟨k, hkmem, hk⟩ := hbit
    rw [List.mem_range] at hkmem
    rw [Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨hbitk, hdest⟩ := hk
    subst hdest
    refine ⟨g ^ (k / d2) * h ^ (k % d2), ⟨k, hkmem, hbitk, rfl⟩, ?_⟩
    have hgg : g ^ ((k / d2 + s) % d1) = g ^ (k / d2 + s) :=
      pow_mod_d d1 g hg1 _
    have hhh : h ^ ((k % d2 + t) % d2) = h ^ (k % d2 + t) :=
      pow_mod_d d2 h hh1 _
    rw [idx_div d2 hd2 (Nat.mod_lt _ hd2), idx_mod d2 (Nat.mod_lt _ hd2),
      hgg, hhh, pow_add, pow_add]
    ring
  · rintro ⟨y, ⟨k, hk, hbitk, rfl⟩, rfl⟩
    refine ⟨(k / d2 + s) % d1 * d2 + (k % d2 + t) % d2,
      idx_lt d1 d2 (Nat.mod_lt _ hd1) (Nat.mod_lt _ hd2), ?_, ?_⟩
    · rw [testBit_rot2, List.any_eq_true]
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hbitk, rfl⟩
    · have hgg : g ^ ((k / d2 + s) % d1) = g ^ (k / d2 + s) :=
        pow_mod_d d1 g hg1 _
      have hhh : h ^ ((k % d2 + t) % d2) = h ^ (k % d2 + t) :=
        pow_mod_d d2 h hh1 _
      rw [idx_div d2 hd2 (Nat.mod_lt _ hd2), idx_mod d2 (Nat.mod_lt _ hd2),
        hgg, hhh, pow_add, pow_add]
      ring

/-- The product-mask step: accumulate rotations by `(v·e, w·e)` for
`e ≤ b` — the mask-side image of `step` with class `g^v · h^w`. -/
def mstep2 (M v w b : ℕ) : ℕ :=
  (List.range (b + 1)).foldl
    (fun acc e => acc ||| rot2 d1 d2 M (v * e) (w * e)) 0

lemma mstep2_lt (hd1 : 0 < d1) (hd2 : 0 < d2) (M v w b : ℕ) :
    mstep2 d1 d2 M v w b < 2 ^ (d1 * d2) := by
  unfold mstep2
  induction b with
  | zero =>
      simpa using rot2_lt d1 d2 hd1 hd2 M 0 0
  | succ b ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      exact Nat.or_lt_two_pow ih (rot2_lt d1 d2 hd1 hd2 M _ _)

/-- **`mstep2` represents `step`** with class `g^v · h^w` and budget
`b` — the product-index analogue of `maskSet_mstep`. -/
lemma maskSet2_mstep2 (hg1 : g ^ d1 = 1) (hh1 : h ^ d2 = 1)
    (hd1 : 0 < d1) (hd2 : 0 < d2) {M : ℕ} (hM : M < 2 ^ (d1 * d2))
    (v w b : ℕ) :
    maskSet2 d1 d2 g h (mstep2 d1 d2 M v w b) =
      step (maskSet2 d1 d2 g h M) (g ^ v * h ^ w, b) := by
  induction b with
  | zero =>
      have h0 : mstep2 d1 d2 M v w 0 = M := by
        change (List.range 1).foldl _ 0 = M
        simp only [List.range_one, List.foldl_cons, List.foldl_nil,
          Nat.mul_zero, Nat.zero_or]
        exact rot2_zero d1 d2 hd1 hd2 hM
      rw [h0]
      ext z
      simp only [mem_step, Nat.le_zero]
      constructor
      · intro hz; exact ⟨z, hz, 0, rfl, by simp⟩
      · rintro ⟨s, hs, e, rfl, rfl⟩; simpa using hs
  | succ b ih =>
      have hsplit : mstep2 d1 d2 M v w (b + 1) =
          mstep2 d1 d2 M v w b |||
            rot2 d1 d2 M (v * (b + 1)) (w * (b + 1)) := by
        unfold mstep2
        rw [List.range_succ, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
      rw [hsplit, maskSet2_or, ih,
        maskSet2_rot2 d1 d2 g h hg1 hh1 hd1 hd2]
      ext z
      simp only [mem_union, mem_step, mem_image]
      constructor
      · rintro (⟨s, hs, e, he, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨s, hs, e, by omega, rfl⟩
        · refine ⟨y, hy, b + 1, le_rfl, ?_⟩
          rw [mul_pow, ← pow_mul, ← pow_mul]
      · rintro ⟨s, hs, e, he, rfl⟩
        rcases Nat.le_succ_iff.mp he with he' | rfl
        · exact Or.inl ⟨s, hs, e, he', rfl⟩
        · refine Or.inr ⟨s, hs, ?_⟩
          rw [mul_pow, ← pow_mul, ← pow_mul]

/-- The full product-mask fold over a list of (log-pair, budget)
triples represents the `reach` fold over the corresponding
(class, budget) pairs. -/
lemma maskSet2_maskFold2 (hg1 : g ^ d1 = 1) (hh1 : h ^ d2 = 1)
    (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ∀ (l : List (ℕ × ℕ × ℕ)) {M : ℕ}, M < 2 ^ (d1 * d2) →
      (l.map (fun vwb => (g ^ vwb.1 * h ^ vwb.2.1, vwb.2.2))).foldl step
          (maskSet2 d1 d2 g h M) =
        maskSet2 d1 d2 g h
          (l.foldl (fun b vwb => mstep2 d1 d2 b vwb.1 vwb.2.1 vwb.2.2) M)
  | [], M, _ => by simp
  | vwb :: l, M, hM => by
      simp only [List.map_cons, List.foldl_cons]
      rw [← maskSet2_mstep2 d1 d2 g h hg1 hh1 hd1 hd2 hM vwb.1 vwb.2.1
        vwb.2.2]
      exact maskSet2_maskFold2 hg1 hh1 hd1 hd2 l
        (mstep2_lt d1 d2 hd1 hd2 M _ _ _)

/-- **`reach` of the mapped list, from the product-mask fold started
at mask `1`** (representing `{1}`) — the product-index analogue of
`reach_eq_maskSet`. -/
lemma reach_eq_maskSet2 (hg1 : g ^ d1 = 1) (hh1 : h ^ d2 = 1)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (l : List (ℕ × ℕ × ℕ)) :
    reach (l.map (fun vwb => (g ^ vwb.1 * h ^ vwb.2.1, vwb.2.2))) =
      maskSet2 d1 d2 g h
        (l.foldl (fun b vwb => mstep2 d1 d2 b vwb.1 vwb.2.1 vwb.2.2) 1) := by
  have hdd : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have h1 : (1 : ℕ) < 2 ^ (d1 * d2) := by
    have := Nat.one_lt_two_pow_iff (n := d1 * d2)
    omega
  have hset : ({1} : Finset (ZMod R)) = maskSet2 d1 d2 g h 1 := by
    ext x
    simp only [mem_singleton, mem_maskSet2]
    constructor
    · rintro rfl
      exact ⟨0, hdd, by simp [Nat.testBit], by simp⟩
    · rintro ⟨k, hk, hbit, rfl⟩
      have hk0 : k = 0 := by
        by_contra hne
        rw [show (1 : ℕ) = 2 ^ 0 from rfl,
          Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hbit
        exact absurd hbit (by simp)
      subst hk0; simp
  rw [reach, hset]
  exact maskSet2_maskFold2 d1 d2 g h hg1 hh1 hd1 hd2 l h1

end ProductMask

/-! ### The R = 15 instantiation: Theorem A‴ (paper Theorem 1.6) -/

section R15Bridge

/-- `11` has order 2 in `(ℤ/15)ˣ`: the `ℤ/2` factor. -/
lemma g15_pow2 : (11 : ZMod 15) ^ 2 = 1 := by decide

/-- `7` has order 4 in `(ℤ/15)ˣ`: the `ℤ/4` factor. -/
lemma h15_pow4 : (7 : ZMod 15) ^ 4 = 1 := by decide

/-- `(i, j) ↦ 11^i · 7^j` is injective on `Fin 2 × Fin 4`: the product
decomposition `(ℤ/15)* = ⟨11⟩ × ⟨7⟩` is exact. -/
lemma gh15_inj : ∀ i < 2, ∀ j < 4, ∀ i' < 2, ∀ j' < 4,
    (11 : ZMod 15) ^ i * 7 ^ j = 11 ^ i' * 7 ^ j' → i = i' ∧ j = j' := by
  -- `decide` cannot synthesize the bounded-`∀` instance directly, so
  -- check the 64 cases over `Fin 2 × Fin 4` squared and transfer.
  have key : ∀ (i i' : Fin 2) (j j' : Fin 4),
      (11 : ZMod 15) ^ i.val * 7 ^ j.val = 11 ^ i'.val * 7 ^ j'.val →
        i.val = i'.val ∧ j.val = j'.val := by decide
  intro i hi j hj i' hi' j' hj' h
  exact key ⟨i, hi⟩ ⟨i', hi'⟩ ⟨j, hj⟩ ⟨j', hj'⟩ h

lemma neg_inv4_15 : -(4⁻¹ : ZMod 15) = 11 := by
  rw [ZMod.inv_eq_of_mul_eq_one 15 4 4 (by decide)]
  decide

/-- **Theorem A‴, finite verification (R = 15)**, in product-index
mask coordinates. Dictionary (class ↦ (i, j) with class = 11^i·7^j):
`1 ↦ (0,0), 7 ↦ (0,1), 4 ↦ (0,2), 13 ↦ (0,3), 11 ↦ (1,0), 2 ↦ (1,1),
14 ↦ (1,2), 8 ↦ (1,3)`; bit index is `4i + j`. `c_u` is the (capped)
multiplicity of the unit class `u` among the prime factors of
`a = (p+15)/4` (caps at 5: the Carmichael exponent is λ(15) = 4, so
multiplicities 0..5 capture every pair of reach-saturation state and
class product); each class enters with exponent budget `2·c_u`, and
`p` (class `7^(2·pe)`, i.e. `1` or `4`) with budget 2.

Structure at hard primes: `2 ∣ a` forces `c₂ ≥ 1`; the two consistency
congruences are `∏ classes ≡ a ≡ 4p (mod 15)` read off in the two
product coordinates (`4p = 7^(2+2·pe)`, and the `i`/`j` coordinates of
the eight classes as in the dictionary). The target
`−m ≡ −4p² ≡ 11 (mod 15)` for both `p`-classes is bit `4·1 + 0 = 4`.

Claim (the exact criterion, all 349,920 consistent configurations):
the target is reachable **iff** some factor class has Jacobi symbol
`−1` mod 15 — i.e. one of `7, 11, 13, 14` is present. No budget
failure shapes (contrast Theorem A″ at R = 11): 349,380 successes,
540 failures, every failure all-residue. -/
theorem theoremA'''_finite_R15 :
    ∀ (c1 c7 c4 c13 c11 c2 c14 c8 : Fin 6) (pe : Fin 2),
      1 ≤ c2.val →
      (c11.val + c2.val + c14.val + c8.val) % 2 = 0 →
      (c7.val + 2 * c4.val + 3 * c13.val + c2.val + 2 * c14.val +
          3 * c8.val) % 4 = (2 + 2 * pe.val) % 4 →
      (Nat.testBit
          ([(0, 0, 2 * c1.val), (0, 1, 2 * c7.val), (0, 2, 2 * c4.val),
            (0, 3, 2 * c13.val), (1, 0, 2 * c11.val), (1, 1, 2 * c2.val),
            (1, 2, 2 * c14.val), (1, 3, 2 * c8.val),
            (0, 2 * pe.val, 2)].foldl
              (fun b vwb => mstep2 2 4 b vwb.1 vwb.2.1 vwb.2.2) 1) 4 = true
        ↔ (c7 ≠ 0 ∨ c11 ≠ 0 ∨ c13 ≠ 0 ∨ c14 ≠ 0)) := by
  native_decide

set_option maxHeartbeats 1600000 in
-- the `decide`-heavy dictionary rewrites below exceed the default limit
/-- **Theorem A‴, multiplicative form** (the product-index bridge
applied to `theoremA'''_finite_R15`; the paper's Theorem 1.6, finite
verification). `c_u` is the capped multiplicity of the unit class `u`
among the prime factors of `a = (p+15)/4` (caps at 5, λ(15) = 4);
`2 ∣ a` forces `c₂ ≥ 1`; hard primes have `p ≡ 1, 4 (mod 15)`;
consistency forces `∏ classes = 4p`. Then the target
`−m = −4⁻¹p² ≡ 11 (mod 15)` is reachable **iff** some factor class
has Jacobi symbol `−1` mod 15, i.e. lies in `{7, 11, 13, 14}` — with
no budget failure shapes at all. Derived symbolically from the mask
theorem: inherits its single `native_decide` axiom and nothing else. -/
theorem theoremA'''_finite_R15_mult :
    ∀ (c1 c7 c4 c13 c11 c2 c14 c8 : Fin 6),
      1 ≤ c2.val →
      ∀ p : ZMod 15, (p = 1 ∨ p = 4) →
      (1 : ZMod 15) ^ c1.val * 7 ^ c7.val * 4 ^ c4.val * 13 ^ c13.val *
          11 ^ c11.val * 2 ^ c2.val * 14 ^ c14.val * 8 ^ c8.val = 4 * p →
      (-(4⁻¹ : ZMod 15) * p ^ 2 ∈
          reach [((1 : ZMod 15), 2 * c1.val), (7, 2 * c7.val),
            (4, 2 * c4.val), (13, 2 * c13.val), (11, 2 * c11.val),
            (2, 2 * c2.val), (14, 2 * c14.val), (8, 2 * c8.val), (p, 2)]
        ↔ (c7 ≠ 0 ∨ c11 ≠ 0 ∨ c13 ≠ 0 ∨ c14 ≠ 0)) := by
  intro c1 c7 c4 c13 c11 c2 c14 c8 hc2 p hp hcons
  -- `p` in product coordinates: `p = 7^(2·pe)`
  obtain ⟨pe, hpe⟩ : ∃ pe : Fin 2, p = (7 : ZMod 15) ^ (2 * pe.val) := by
    rcases hp with rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
  -- consistency, rewritten through the product dictionary
  have hIJ : (11 : ZMod 15) ^ (c11.val + c2.val + c14.val + c8.val) *
      7 ^ (c7.val + 2 * c4.val + 3 * c13.val + c2.val + 2 * c14.val +
        3 * c8.val) = 7 ^ (2 + 2 * pe.val) := by
    calc (11 : ZMod 15) ^ (c11.val + c2.val + c14.val + c8.val) *
        7 ^ (c7.val + 2 * c4.val + 3 * c13.val + c2.val + 2 * c14.val +
          3 * c8.val)
        = (1 : ZMod 15) ^ c1.val * 7 ^ c7.val * 4 ^ c4.val *
            13 ^ c13.val * 11 ^ c11.val * 2 ^ c2.val * 14 ^ c14.val *
            8 ^ c8.val := by
          rw [show (4 : ZMod 15) = 7 ^ 2 from by decide,
            show (13 : ZMod 15) = 7 ^ 3 from by decide,
            show (2 : ZMod 15) = 11 * 7 from by decide,
            show (14 : ZMod 15) = 11 * 7 ^ 2 from by decide,
            show (8 : ZMod 15) = 11 * 7 ^ 3 from by decide]
          simp only [one_pow, mul_pow, ← pow_mul]
          ring
      _ = 4 * p := hcons
      _ = 7 ^ (2 + 2 * pe.val) := by
          rw [hpe, show (4 : ZMod 15) = 7 ^ 2 from by decide, ← pow_add]
  -- the two consistency congruences of the mask theorem
  have hkey : (c11.val + c2.val + c14.val + c8.val) % 2 = 0 ∧
      (c7.val + 2 * c4.val + 3 * c13.val + c2.val + 2 * c14.val +
        3 * c8.val) % 4 = (2 + 2 * pe.val) % 4 := by
    have hred : (11 : ZMod 15) ^
        ((c11.val + c2.val + c14.val + c8.val) % 2) *
        7 ^ ((c7.val + 2 * c4.val + 3 * c13.val + c2.val + 2 * c14.val +
          3 * c8.val) % 4) = 11 ^ 0 * 7 ^ ((2 + 2 * pe.val) % 4) := by
      rw [pow_mod_d 2 (11 : ZMod 15) g15_pow2,
        pow_mod_d 4 (7 : ZMod 15) h15_pow4,
        pow_mod_d 4 (7 : ZMod 15) h15_pow4, pow_zero, one_mul, hIJ]
    exact gh15_inj _ (Nat.mod_lt _ (by norm_num))
      _ (Nat.mod_lt _ (by norm_num)) 0 (by norm_num)
      _ (Nat.mod_lt _ (by norm_num)) hred
  -- the mask theorem instance
  have hmask := theoremA'''_finite_R15 c1 c7 c4 c13 c11 c2 c14 c8 pe hc2
    hkey.1 hkey.2
  -- the configuration list is the mapped product-log list
  have hLc : ([((1 : ZMod 15), 2 * c1.val), (7, 2 * c7.val),
      (4, 2 * c4.val), (13, 2 * c13.val), (11, 2 * c11.val),
      (2, 2 * c2.val), (14, 2 * c14.val), (8, 2 * c8.val), (p, 2)] :
        List (ZMod 15 × ℕ)) =
      ([(0, 0, 2 * c1.val), (0, 1, 2 * c7.val), (0, 2, 2 * c4.val),
        (0, 3, 2 * c13.val), (1, 0, 2 * c11.val), (1, 1, 2 * c2.val),
        (1, 2, 2 * c14.val), (1, 3, 2 * c8.val),
        (0, 2 * pe.val, 2)] : List (ℕ × ℕ × ℕ)).map
          (fun vwb => ((11 : ZMod 15) ^ vwb.1 * 7 ^ vwb.2.1, vwb.2.2)) := by
    simp only [List.map_cons, List.map_nil]
    rw [show (11 : ZMod 15) ^ 0 * 7 ^ 0 = 1 from by decide,
      show (11 : ZMod 15) ^ 0 * 7 ^ 1 = 7 from by decide,
      show (11 : ZMod 15) ^ 0 * 7 ^ 2 = 4 from by decide,
      show (11 : ZMod 15) ^ 0 * 7 ^ 3 = 13 from by decide,
      show (11 : ZMod 15) ^ 1 * 7 ^ 0 = 11 from by decide,
      show (11 : ZMod 15) ^ 1 * 7 ^ 1 = 2 from by decide,
      show (11 : ZMod 15) ^ 1 * 7 ^ 2 = 14 from by decide,
      show (11 : ZMod 15) ^ 1 * 7 ^ 3 = 8 from by decide,
      show (11 : ZMod 15) ^ 0 * 7 ^ (2 * pe.val) = p from by
        rw [pow_zero, one_mul, hpe]]
  have hreach : reach ([((1 : ZMod 15), 2 * c1.val), (7, 2 * c7.val),
      (4, 2 * c4.val), (13, 2 * c13.val), (11, 2 * c11.val),
      (2, 2 * c2.val), (14, 2 * c14.val), (8, 2 * c8.val), (p, 2)] :
        List (ZMod 15 × ℕ)) =
      maskSet2 2 4 (11 : ZMod 15) 7
        ([(0, 0, 2 * c1.val), (0, 1, 2 * c7.val), (0, 2, 2 * c4.val),
          (0, 3, 2 * c13.val), (1, 0, 2 * c11.val), (1, 1, 2 * c2.val),
          (1, 2, 2 * c14.val), (1, 3, 2 * c8.val),
          (0, 2 * pe.val, 2)].foldl
            (fun b vwb => mstep2 2 4 b vwb.1 vwb.2.1 vwb.2.2) 1) := by
    rw [hLc]
    exact reach_eq_maskSet2 2 4 (11 : ZMod 15) 7 g15_pow2 h15_pow4
      (by norm_num) (by norm_num) _
  -- the target class in product coordinates
  have htarget : (11 : ZMod 15) ^ 1 * 7 ^ 0 = -(4⁻¹ : ZMod 15) * p ^ 2 := by
    rw [neg_inv4_15]
    rcases hp with rfl | rfl <;> decide
  -- membership ↔ the target bit
  have hmem_iff : (-(4⁻¹ : ZMod 15) * p ^ 2 ∈
      maskSet2 2 4 (11 : ZMod 15) 7
        ([(0, 0, 2 * c1.val), (0, 1, 2 * c7.val), (0, 2, 2 * c4.val),
          (0, 3, 2 * c13.val), (1, 0, 2 * c11.val), (1, 1, 2 * c2.val),
          (1, 2, 2 * c14.val), (1, 3, 2 * c8.val),
          (0, 2 * pe.val, 2)].foldl
            (fun b vwb => mstep2 2 4 b vwb.1 vwb.2.1 vwb.2.2) 1)) ↔
      Nat.testBit
        ([(0, 0, 2 * c1.val), (0, 1, 2 * c7.val), (0, 2, 2 * c4.val),
          (0, 3, 2 * c13.val), (1, 0, 2 * c11.val), (1, 1, 2 * c2.val),
          (1, 2, 2 * c14.val), (1, 3, 2 * c8.val),
          (0, 2 * pe.val, 2)].foldl
            (fun b vwb => mstep2 2 4 b vwb.1 vwb.2.1 vwb.2.2) 1) 4 = true := by
    constructor
    · intro hm
      rw [mem_maskSet2] at hm
      obtain ⟨k, hk, hbit, hpow⟩ := hm
      obtain ⟨h1, h2⟩ := gh15_inj (k / 4) (by omega) (k % 4) (by omega)
        1 (by norm_num) 0 (by norm_num) (hpow.trans htarget.symm)
      have hk4 : k = 4 := by omega
      rwa [hk4] at hbit
    · intro hbit
      rw [mem_maskSet2]
      refine ⟨4, by norm_num, hbit, ?_⟩
      rw [show (4 : ℕ) / 4 = 1 from rfl, show (4 : ℕ) % 4 = 0 from rfl]
      exact htarget
  rw [hreach]
  exact hmem_iff.trans hmask

end R15Bridge

end ErdosStraus

-- Audit. The product-index bridge layer is symbolic (standard axioms
-- only); the mask enumeration reports its single `native_decide` axiom,
-- and the multiplicative form inherits exactly that axiom and nothing
-- else — the bridge adds no computational trust.
#print axioms ErdosStraus.maskSet2_rot2
#print axioms ErdosStraus.maskSet2_mstep2
#print axioms ErdosStraus.reach_eq_maskSet2
#print axioms ErdosStraus.theoremA'''_finite_R15
#print axioms ErdosStraus.theoremA'''_finite_R15_mult
