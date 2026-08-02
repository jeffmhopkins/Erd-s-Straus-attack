/-
The discrete-log bridges: from the mask-coordinate finite checks of
`Enumerations.lean` back to the multiplicative `reach` model.

The computational theorems (`lemmaS_finite_R19`, `lemmaS_finite_R23`,
`theoremA''_finite_R11`) are stated over rotation masks in discrete-log
coordinates because that is what Lean's evaluator can check quickly.
This file proves the translation *symbolically*: a mask represents a
set of unit classes (`maskSet`), rotation represents multiplication by
`g^s` (`maskSet_rotg`), the accumulate-rotations step represents the
divisor-class `step` (`maskSet_mstep`), and the whole mask fold
represents `reach` (`maskSet_maskFold`). The only per-modulus inputs
are `g^d = 1`, injectivity of `i ↦ g^i` below `d`, and the concrete
discrete-log function — all discharged by `decide`.

Main results: `lemmaS_finite_R19_mult`, `lemmaS_finite_R23_mult` (the
support-bound checks restated over `ZMod 19` / `ZMod 23` and the
multiplicative `reach` model) and `theoremA''_finite_R11_mult`
(Theorem A″'s exact criterion restated over `ZMod 11`, including the
two-case failure classification) — each derived from its mask theorem
with no new enumeration, so each inherits exactly one `native_decide`
axiom and nothing else.
-/
import ErdosStraus.Enumerations

namespace ErdosStraus

open Finset

/-! ### Parametric bit-mask layer -/

section BitBridge

variable {R : ℕ} (d : ℕ) (g : ZMod R)

/-- Generic cyclic rotation of a `d`-bit mask (`rot18`, `rot10`,
`rot22` are its instances). -/
def rotg (M s : ℕ) : ℕ :=
  ((M <<< (s % d)) ||| (M >>> (d - s % d))) % 2 ^ d

lemma rot18_eq_rotg (M s : ℕ) : rot18 M s = rotg 18 M s := by
  unfold rot18 rotg
  rw [Nat.and_two_pow_sub_one_eq_mod]

lemma rot10_eq_rotg (M s : ℕ) : rot10 M s = rotg 10 M s := by
  unfold rot10 rotg
  rw [Nat.and_two_pow_sub_one_eq_mod]

lemma rot22_eq_rotg (M s : ℕ) : rot22 M s = rotg 22 M s := by
  unfold rot22 rotg
  rw [Nat.and_two_pow_sub_one_eq_mod]

lemma rotg_lt (M s : ℕ) : rotg d M s < 2 ^ d :=
  Nat.mod_lt _ (Nat.two_pow_pos d)

/-- Reduction of `x % d` when `x < 2d`: subtract `d` at most once.
Keeps all later index arithmetic linear (`omega` cannot handle `% d`
with variable `d`). -/
lemma mod_two_d {d : ℕ} (_hd : 0 < d) {x : ℕ} (hx : x < 2 * d) :
    x % d = if x < d then x else x - d := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · have h2 : x = (x - d) + d := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The rotation amount only matters modulo `d`. -/
lemma rotg_mod (hd : 0 < d) (M s : ℕ) :
    rotg d M s = rotg d M (s % d) := by
  unfold rotg
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hd)]

/-- Bit `i` of the rotation is bit `(i - s) mod d` of the original
(for a reduced rotation amount `s < d`). -/
lemma testBit_rotg (hd : 0 < d) {M : ℕ} (hM : M < 2 ^ d) {s : ℕ}
    (hs : s < d) {i : ℕ} (hi : i < d) :
    (rotg d M s).testBit i = M.testBit ((i + (d - s)) % d) := by
  unfold rotg
  rw [Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    mod_two_d hd (by omega)]
  by_cases h : s ≤ i
  · have hif : ¬ (i + (d - s) < d) := by omega
    have harg : i + (d - s) - d = i - s := by omega
    have hdead : M.testBit (d - s + i) = false := by
      apply Nat.testBit_lt_two_pow
      calc M < 2 ^ d := hM
        _ ≤ 2 ^ (d - s + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hif, harg, hdead, h, hi]
  · have hif : i + (d - s) < d := by omega
    simp only [if_pos hif]
    have : ¬ (i ≥ s) := h
    simp [this, hi, Nat.add_comm i (d - s)]

/-- Rotation by `0` is the identity on masks below `2^d`. -/
lemma rotg_zero (hd : 0 < d) {M : ℕ} (hM : M < 2 ^ d) :
    rotg d M 0 = M := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < d
  · rw [testBit_rotg d hd hM hd hi, Nat.sub_zero,
      mod_two_d hd (by omega), if_neg (by omega)]
    congr 1
    omega
  · have h1 : (rotg d M 0).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc rotg d M 0 < 2 ^ d := rotg_lt d M 0
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : M.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc M < 2 ^ d := hM
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h1, h2]

/-- The set of unit classes represented by a mask: bit `i` stands for
the class `g^i`. -/
def maskSet (M : ℕ) : Finset (ZMod R) :=
  ((Finset.range d).filter (fun i => M.testBit i)).image (g ^ ·)

lemma mem_maskSet {M : ℕ} {x : ZMod R} :
    x ∈ maskSet d g M ↔ ∃ i, i < d ∧ M.testBit i ∧ g ^ i = x := by
  simp only [maskSet, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hbit⟩, rfl⟩; exact ⟨i, hi, hbit, rfl⟩
  · rintro ⟨i, hi, hbit, rfl⟩; exact ⟨i, ⟨hi, hbit⟩, rfl⟩

lemma maskSet_or (M N : ℕ) :
    maskSet d g (M ||| N) = maskSet d g M ∪ maskSet d g N := by
  ext x
  simp only [mem_maskSet, mem_union, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, hbit | hbit, rfl⟩
    · exact Or.inl ⟨i, hi, hbit, rfl⟩
    · exact Or.inr ⟨i, hi, hbit, rfl⟩
  · rintro (⟨i, hi, hbit, rfl⟩ | ⟨i, hi, hbit, rfl⟩)
    · exact ⟨i, hi, Or.inl hbit, rfl⟩
    · exact ⟨i, hi, Or.inr hbit, rfl⟩

/-- Exponents of `g` only matter modulo `d`. -/
lemma pow_mod_d (hg1 : g ^ d = 1) (k : ℕ) : g ^ (k % d) = g ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k d, pow_add, pow_mul, hg1, one_pow,
    one_mul]

/-- Rotation is multiplication by `g^s` on represented sets (reduced
rotation amount). -/
lemma maskSet_rotg_lt (hg1 : g ^ d = 1) (hd : 0 < d) {M : ℕ}
    (hM : M < 2 ^ d) {s : ℕ} (hs : s < d) :
    maskSet d g (rotg d M s) = (maskSet d g M).image (· * g ^ s) := by
  ext x
  simp only [mem_maskSet, mem_image]
  constructor
  · rintro ⟨i, hi, hbit, rfl⟩
    rw [testBit_rotg d hd hM hs hi] at hbit
    rw [mod_two_d hd (by omega)] at hbit
    by_cases h : s ≤ i
    · rw [if_neg (by omega), show i + (d - s) - d = i - s from by omega]
        at hbit
      exact ⟨g ^ (i - s), ⟨i - s, by omega, hbit, rfl⟩,
        by rw [← pow_add, show i - s + s = i from by omega]⟩
    · rw [if_pos (by omega)] at hbit
      refine ⟨g ^ (i + (d - s)), ⟨i + (d - s), by omega, hbit, rfl⟩, ?_⟩
      rw [← pow_add, show i + (d - s) + s = i + d from by omega, pow_add,
        hg1, mul_one]
  · rintro ⟨y, ⟨j, hj, hbit, rfl⟩, rfl⟩
    refine ⟨(j + s) % d, Nat.mod_lt _ hd, ?_, ?_⟩
    · rw [testBit_rotg d hd hM hs (Nat.mod_lt _ hd)]
      have hf : (j + s) % d < d := Nat.mod_lt _ hd
      rw [mod_two_d hd (show (j + s) % d + (d - s) < 2 * d by omega),
        mod_two_d hd (show j + s < 2 * d by omega)]
      by_cases h : j + s < d
      · rw [if_pos h, if_neg (by omega),
          show j + s + (d - s) - d = j from by omega]
        exact hbit
      · rw [if_neg h, if_pos (by omega),
          show j + s - d + (d - s) = j from by omega]
        exact hbit
    · rw [mod_two_d hd (show j + s < 2 * d by omega)]
      by_cases h : j + s < d
      · rw [if_pos h, pow_add]
      · rw [if_neg h, show g ^ (j + s - d) = g ^ (j + s - d) * 1 from
          (mul_one _).symm, ← hg1, ← pow_add,
          show j + s - d + d = j + s from by omega, pow_add]

/-- Rotation is multiplication by `g^s` on represented sets. -/
lemma maskSet_rotg (hg1 : g ^ d = 1) (hd : 0 < d) {M : ℕ}
    (hM : M < 2 ^ d) (s : ℕ) :
    maskSet d g (rotg d M s) = (maskSet d g M).image (· * g ^ s) := by
  rw [rotg_mod d hd, maskSet_rotg_lt d g hg1 hd hM (Nat.mod_lt _ hd),
    pow_mod_d d g hg1]

end BitBridge

/-! ### The mask fold represents `reach` -/

section FoldBridge

variable {R : ℕ} (d : ℕ) (g : ZMod R)

/-- Membership in one divisor-class step. -/
lemma mem_step {A : Finset (ZMod R)} {x : ZMod R} {b : ℕ} {z : ZMod R} :
    z ∈ step A (x, b) ↔ ∃ s ∈ A, ∃ e ≤ b, s * x ^ e = z := by
  simp only [step, mem_biUnion, mem_image, powers, mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨s, hs, w, ⟨e, he, rfl⟩, rfl⟩; exact ⟨s, hs, e, he, rfl⟩
  · rintro ⟨s, hs, e, he, rfl⟩; exact ⟨s, hs, _, ⟨e, he, rfl⟩, rfl⟩

/-- The mask-side step: accumulate rotations by `v·e` for `e ≤ b`. -/
def mstep (M v b : ℕ) : ℕ :=
  (List.range (b + 1)).foldl (fun acc e => acc ||| rotg d M (v * e)) 0

lemma mstep_lt (M v b : ℕ) : mstep d M v b < 2 ^ d := by
  unfold mstep
  induction b with
  | zero => simpa using rotg_lt d M 0
  | succ b ih =>
      rw [List.range_succ, List.foldl_append]
      exact Nat.or_lt_two_pow ih (rotg_lt d M _)

/-- `mstep` represents `step` with class `g^v` and budget `b`. -/
lemma maskSet_mstep (hg1 : g ^ d = 1) (hd : 0 < d) {M : ℕ}
    (hM : M < 2 ^ d) (v b : ℕ) :
    maskSet d g (mstep d M v b) = step (maskSet d g M) (g ^ v, b) := by
  induction b with
  | zero =>
      have h0 : mstep d M v 0 = M := by
        simp [mstep, List.range_succ, rotg_zero d hd hM]
      rw [h0]
      ext z
      simp only [mem_step, Nat.le_zero]
      constructor
      · intro hz; exact ⟨z, hz, 0, rfl, by simp⟩
      · rintro ⟨s, hs, e, rfl, rfl⟩; simpa using hs
  | succ b ih =>
      have hsplit : mstep d M v (b + 1) =
          mstep d M v b ||| rotg d M (v * (b + 1)) := by
        unfold mstep
        rw [List.range_succ, List.foldl_append]
        rfl
      rw [hsplit, maskSet_or, ih, maskSet_rotg d g hg1 hd hM _]
      ext z
      simp only [mem_union, mem_step, mem_image]
      constructor
      · rintro (⟨s, hs, e, he, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨s, hs, e, by omega, rfl⟩
        · exact ⟨y, hy, b + 1, le_rfl, by rw [← pow_mul]⟩
      · rintro ⟨s, hs, e, he, rfl⟩
        rcases Nat.le_succ_iff.mp he with he' | rfl
        · exact Or.inl ⟨s, hs, e, he', rfl⟩
        · exact Or.inr ⟨s, hs, by rw [← pow_mul]⟩

/-- The full mask fold over a list of (log, budget) pairs represents
the `reach` fold over the corresponding (class, budget) pairs. -/
lemma maskSet_maskFold (hg1 : g ^ d = 1) (hd : 0 < d) :
    ∀ (l : List (ℕ × ℕ)) {M : ℕ}, M < 2 ^ d →
      (l.map (fun vb => (g ^ vb.1, vb.2))).foldl step (maskSet d g M) =
        maskSet d g (l.foldl (fun b vb => mstep d b vb.1 vb.2) M)
  | [], M, _ => by simp
  | vb :: l, M, hM => by
      simp only [List.map_cons, List.foldl_cons]
      rw [← maskSet_mstep d g hg1 hd hM vb.1 vb.2]
      exact maskSet_maskFold hg1 hd l (mstep_lt d M vb.1 vb.2)

/-- `reach` of the mapped list, from the mask fold started at mask `1`
(representing `{1}`). -/
lemma reach_eq_maskSet (hg1 : g ^ d = 1) (hd : 0 < d) (l : List (ℕ × ℕ)) :
    reach (l.map (fun vb => (g ^ vb.1, vb.2))) =
      maskSet d g (l.foldl (fun b vb => mstep d b vb.1 vb.2) 1) := by
  have h1 : (1 : ℕ) < 2 ^ d := by
    have := Nat.one_lt_two_pow_iff (n := d)
    omega
  have hset : ({1} : Finset (ZMod R)) = maskSet d g 1 := by
    ext x
    simp only [mem_singleton, mem_maskSet]
    constructor
    · rintro rfl
      exact ⟨0, hd, by simp [Nat.testBit], by simp⟩
    · rintro ⟨i, hi, hbit, rfl⟩
      have : i = 0 := by
        by_contra hne
        rw [show (1 : ℕ) = 2 ^ 0 from rfl,
          Nat.testBit_two_pow_of_ne (Ne.symm hne)] at hbit
        exact absurd hbit (by simp)
      subst this; simp
  rw [reach, hset]
  exact maskSet_maskFold d g hg1 hd l h1

/-- `step` is right-commutative, so `reach` is invariant under
permutations of the configuration list. -/
lemma step_right_comm (A : Finset (ZMod R)) (a b : ZMod R × ℕ) :
    step (step A a) b = step (step A b) a := by
  obtain ⟨xa, ba⟩ := a
  obtain ⟨xb, bb⟩ := b
  ext z
  simp only [mem_step]
  constructor
  · rintro ⟨s, ⟨t, ht, e, he, rfl⟩, e', he', rfl⟩
    exact ⟨t * xb ^ e', ⟨t, ht, e', he', rfl⟩, e, he, by ring⟩
  · rintro ⟨s, ⟨t, ht, e, he, rfl⟩, e', he', rfl⟩
    exact ⟨t * xa ^ e', ⟨t, ht, e', he', rfl⟩, e, he, by ring⟩

lemma reach_perm {l l' : List (ZMod R × ℕ)} (h : l.Perm l') :
    reach l = reach l' :=
  h.foldl_eq' (fun x _ y _ z => step_right_comm z x y) {1}

lemma reach_append_single (l : List (ZMod R × ℕ)) (xb : ZMod R × ℕ) :
    reach (l ++ [xb]) = step (reach l) xb := by
  simp [reach, List.foldl_append]

/-- Budget-2 `mstep` is the triple-or of the mask theorems. -/
lemma mstep_two (hd : 0 < d) {M : ℕ} (hM : M < 2 ^ d) (v : ℕ) :
    mstep d M v 2 = M ||| rotg d M v ||| rotg d M (2 * v) := by
  show (List.range 3).foldl (fun acc e => acc ||| rotg d M (v * e)) 0 = _
  rw [show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.mul_one,
    Nat.zero_or, rotg_zero d hd hM]
  rw [Nat.mul_comm v 2]

/-- Budget-0 `mstep` is the identity on masks below `2^d`. -/
lemma mstep_zero (hd : 0 < d) {M : ℕ} (hM : M < 2 ^ d) (v : ℕ) :
    mstep d M v 0 = M := by
  show (List.range 1).foldl (fun acc e => acc ||| rotg d M (v * e)) 0 = _
  rw [show List.range 1 = [0] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_or,
    rotg_zero d hd hM]

end FoldBridge

/-! ### The R = 19 bridge -/

section R19Bridge

/-- `2` generates `(ℤ/19)ˣ`: the concrete inputs to the bridge. -/
lemma g19_pow18 : (2 : ZMod 19) ^ 18 = 1 := by decide

lemma g19_inj : ∀ i, i < 18 → ∀ j, j < 18 →
    (2 : ZMod 19) ^ i = 2 ^ j → i = j := by decide

/-- Concrete discrete logarithm base 2 mod 19. -/
def log19 (x : ZMod 19) : ℕ :=
  (List.range 18).findIdx (fun i => (2 : ZMod 19) ^ i = x)

lemma log19_spec : ∀ x : ZMod 19, x ≠ 0 →
    log19 x < 18 ∧ (2 : ZMod 19) ^ log19 x = x := by decide

lemma log19_range : ∀ x : ZMod 19, x ≠ 0 → x ≠ 1 →
    1 ≤ log19 x ∧ log19 x ≤ 17 := by decide

lemma neg_inv4_19 : -(4⁻¹ : ZMod 19) = 2 ^ 7 := by
  rw [ZMod.inv_eq_of_mul_eq_one 19 4 5 (by decide)]
  decide

/-- The concrete mask fold of `lemmaS_finite_R19` is the generic
`mstep` fold over the (log, budget-2) list of `S`. -/
lemma r19_fold_eq (S : Finset ℕ) :
    ∀ (l : List ℕ) (M : ℕ), M < 2 ^ 18 →
      l.foldl (fun b v =>
          if v ∈ S then b ||| rot18 b v ||| rot18 b (2 * v) else b) M =
        (l.filterMap fun v =>
            if v ∈ S then some (v, 2) else none).foldl
          (fun b vb => mstep 18 b vb.1 vb.2) M
  | [], _, _ => rfl
  | v :: l, M, hM => by
      by_cases hv : v ∈ S
      · simp only [List.foldl_cons, List.filterMap_cons, if_pos hv]
        rw [show M ||| rot18 M v ||| rot18 M (2 * v) = mstep 18 M v 2 by
          rw [mstep_two 18 (by norm_num) hM, rot18_eq_rotg,
            rot18_eq_rotg]]
        exact r19_fold_eq S l _ (mstep_lt 18 M v 2)
      · simp only [List.foldl_cons, List.filterMap_cons, if_neg hv]
        exact r19_fold_eq S l M hM

/-- **Lemma S at R = 19, multiplicative form** (the discrete-log
bridge applied to `lemmaS_finite_R19`). For every set `T` of nine
unit classes other than 1, every duplicate-free configuration list
enumerating `T` with exponent budget 2, and every nonzero class of
`p`: the target `−4⁻¹p²` is reachable. Derived symbolically from the
mask theorem — no new enumeration. -/
theorem lemmaS_finite_R19_mult
    (T : Finset (ZMod 19))
    (hT : T ∈ Finset.powersetCard 9
      ((Finset.univ : Finset (ZMod 19)).filter fun x => x ≠ 0 ∧ x ≠ 1))
    (l : List (ZMod 19 × ℕ)) (hl : l.Nodup)
    (hmem : ∀ xb : ZMod 19 × ℕ, xb ∈ l ↔ xb.1 ∈ T ∧ xb.2 = 2)
    (p : ZMod 19) (hp : p ≠ 0) :
    -(4⁻¹ : ZMod 19) * p ^ 2 ∈ reach (l ++ [(p, 2)]) := by
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  have hT0 : ∀ x ∈ T, x ≠ 0 ∧ x ≠ 1 := by
    intro x hx
    have := hTsub hx
    simpa using this
  -- the log-coordinate support
  set S : Finset ℕ := T.image log19 with hS_def
  have hS : S ∈ Finset.powersetCard 9 (Finset.Icc 1 17) := by
    rw [Finset.mem_powersetCard]
    constructor
    · intro v hv
      rw [hS_def, Finset.mem_image] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨h0, h1⟩ := hT0 x hx
      have := log19_range x h0 h1
      rw [Finset.mem_Icc]
      omega
    · rw [hS_def, Finset.card_image_of_injOn, hTcard]
      intro x hx y hy hxy
      have hx' := (log19_spec x (hT0 x hx).1).2
      have hy' := (log19_spec y (hT0 y hy).1).2
      rw [← hx', ← hy', hxy]
  -- the mask theorem instance
  set plog : ℕ := log19 p with hplog_def
  have hplog : plog < 18 := (log19_spec p hp).1
  have hpexp : (2 : ZMod 19) ^ plog = p := (log19_spec p hp).2
  set B : ℕ := (List.range 18).foldl
    (fun b v => if v ∈ S then b ||| rot18 b v ||| rot18 b (2 * v) else b)
    1 with hB_def
  have hmask : Nat.testBit (B ||| rot18 B plog ||| rot18 B (2 * plog))
      ((2 * plog + 7) % 18) = true :=
    lemmaS_finite_R19 S hS plog hplog
  -- bound on the concrete fold
  have hBlt : B < 2 ^ 18 := by
    rw [hB_def, r19_fold_eq S (List.range 18) 1 (by norm_num)]
    generalize (List.range 18).filterMap _ = L
    induction L using List.reverseRecOn with
    | nil => norm_num
    | append_singleton l' xb _ =>
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact mstep_lt 18 _ xb.1 xb.2
  -- the canonical (log-order) configuration list
  set Ls : List (ℕ × ℕ) := (List.range 18).filterMap
    (fun v => if v ∈ S then some (v, 2) else none) with hLs_def
  have hreachLs : reach (Ls.map fun vb => ((2 : ZMod 19) ^ vb.1, vb.2)) =
      maskSet 18 (2 : ZMod 19) B := by
    rw [reach_eq_maskSet 18 (2 : ZMod 19) g19_pow18 (by norm_num) Ls,
      hB_def, r19_fold_eq S (List.range 18) 1 (by norm_num), hLs_def]
  -- `l` is a permutation of the canonical list
  have hLs_mem : ∀ vb : ℕ × ℕ, vb ∈ Ls ↔ vb.1 ∈ S ∧ vb.2 = 2 := by
    intro vb
    rw [hLs_def, List.mem_filterMap]
    constructor
    · rintro ⟨v, _, hsome⟩
      by_cases hv : v ∈ S
      · rw [if_pos hv] at hsome
        cases hsome
        exact ⟨hv, rfl⟩
      · rw [if_neg hv] at hsome
        cases hsome
    · rintro ⟨hv1, hv2⟩
      refine ⟨vb.1, List.mem_range.mpr ?_, ?_⟩
      · have := hS
        rw [Finset.mem_powersetCard] at this
        have := this.1 hv1
        rw [Finset.mem_Icc] at this
        omega
      · rw [if_pos hv1]
        cases vb
        simp_all
  have hLs_nodup : Ls.Nodup := by
    rw [hLs_def]
    refine List.Nodup.filterMap ?_ (List.nodup_range)
    intro a a' b hb hb'
    by_cases ha : a ∈ S
    · by_cases ha' : a' ∈ S
      · rw [if_pos ha, Option.mem_def, Option.some_inj] at hb
        rw [if_pos ha', Option.mem_def, Option.some_inj] at hb'
        rw [← hb'] at hb
        exact (Prod.ext_iff.mp hb).1
      · rw [if_neg ha'] at hb'
        cases hb'
    · rw [if_neg ha] at hb
      cases hb
  have hmap_nodup : (Ls.map fun vb => ((2 : ZMod 19) ^ vb.1, vb.2)).Nodup := by
    refine List.Nodup.map_on ?_ hLs_nodup
    intro x hx y hy hxy
    have hx1 : x.1 < 18 := by
      have := (hLs_mem x).mp hx
      have h2 := hS
      rw [Finset.mem_powersetCard] at h2
      have := h2.1 this.1
      rw [Finset.mem_Icc] at this
      omega
    have hy1 : y.1 < 18 := by
      have := (hLs_mem y).mp hy
      have h2 := hS
      rw [Finset.mem_powersetCard] at h2
      have := h2.1 this.1
      rw [Finset.mem_Icc] at this
      omega
    obtain ⟨heq1, heq2⟩ := Prod.ext_iff.mp hxy
    have := g19_inj x.1 hx1 y.1 hy1 heq1
    exact Prod.ext this heq2
  have htoFin : l.toFinset =
      (Ls.map fun vb => ((2 : ZMod 19) ^ vb.1, vb.2)).toFinset := by
    ext xb
    rw [List.mem_toFinset, List.mem_toFinset, hmem, List.mem_map]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨(log19 xb.1, 2), ?_, ?_⟩
      · rw [hLs_mem]
        exact ⟨Finset.mem_image_of_mem _ hx1, rfl⟩
      · have := (log19_spec xb.1 (hT0 _ hx1).1).2
        cases xb
        simp_all
    · rintro ⟨⟨v, b2⟩, hvb, rfl⟩
      obtain ⟨hv1, hv2⟩ := (hLs_mem ⟨v, b2⟩).mp hvb
      dsimp only at hv1 hv2 ⊢
      subst hv2
      rw [hS_def, Finset.mem_image] at hv1
      obtain ⟨x, hx, hlog⟩ := hv1
      have hxe := (log19_spec x (hT0 x hx).1).2
      exact ⟨by rw [← hlog, hxe]; exact hx, rfl⟩
  have hperm : l.Perm (Ls.map fun vb => ((2 : ZMod 19) ^ vb.1, vb.2)) :=
    List.perm_of_nodup_nodup_toFinset_eq hl hmap_nodup htoFin
  -- assemble
  rw [reach_append_single, reach_perm hperm, hreachLs, ← hpexp,
    ← maskSet_mstep 18 (2 : ZMod 19) g19_pow18 (by norm_num) hBlt plog 2,
    mstep_two 18 (by norm_num) hBlt plog, ← rot18_eq_rotg, ← rot18_eq_rotg]
  rw [mem_maskSet]
  refine ⟨(2 * plog + 7) % 18, Nat.mod_lt _ (by norm_num), hmask, ?_⟩
  rw [pow_mod_d 18 (2 : ZMod 19) g19_pow18, neg_inv4_19]
  ring

end R19Bridge

/-! ### The R = 23 bridge (same shape, primitive root 5) -/

section R23Bridge

lemma g23_pow22 : (5 : ZMod 23) ^ 22 = 1 := by decide

lemma g23_inj : ∀ i, i < 22 → ∀ j, j < 22 →
    (5 : ZMod 23) ^ i = 5 ^ j → i = j := by decide

/-- Concrete discrete logarithm base 5 mod 23. -/
def log23 (x : ZMod 23) : ℕ :=
  (List.range 22).findIdx (fun i => (5 : ZMod 23) ^ i = x)

lemma log23_spec : ∀ x : ZMod 23, x ≠ 0 →
    log23 x < 22 ∧ (5 : ZMod 23) ^ log23 x = x := by decide

lemma log23_range : ∀ x : ZMod 23, x ≠ 0 → x ≠ 1 →
    1 ≤ log23 x ∧ log23 x ≤ 21 := by decide

lemma neg_inv4_23 : -(4⁻¹ : ZMod 23) = 5 ^ 7 := by
  rw [ZMod.inv_eq_of_mul_eq_one 23 4 6 (by decide)]
  decide

lemma r23_fold_eq (S : Finset ℕ) :
    ∀ (l : List ℕ) (M : ℕ), M < 2 ^ 22 →
      l.foldl (fun b v =>
          if v ∈ S then b ||| rot22 b v ||| rot22 b (2 * v) else b) M =
        (l.filterMap fun v =>
            if v ∈ S then some (v, 2) else none).foldl
          (fun b vb => mstep 22 b vb.1 vb.2) M
  | [], _, _ => rfl
  | v :: l, M, hM => by
      by_cases hv : v ∈ S
      · simp only [List.foldl_cons, List.filterMap_cons, if_pos hv]
        rw [show M ||| rot22 M v ||| rot22 M (2 * v) = mstep 22 M v 2 by
          rw [mstep_two 22 (by norm_num) hM, rot22_eq_rotg,
            rot22_eq_rotg]]
        exact r23_fold_eq S l _ (mstep_lt 22 M v 2)
      · simp only [List.foldl_cons, List.filterMap_cons, if_neg hv]
        exact r23_fold_eq S l M hM

/-- **Lemma S at R = 23, multiplicative form** (the discrete-log
bridge applied to `lemmaS_finite_R23`): for every set `T` of eleven
unit classes other than 1, every duplicate-free configuration list
enumerating `T` with exponent budget 2, and every nonzero class of
`p`, the target `−4⁻¹p²` is reachable. -/
theorem lemmaS_finite_R23_mult
    (T : Finset (ZMod 23))
    (hT : T ∈ Finset.powersetCard 11
      ((Finset.univ : Finset (ZMod 23)).filter fun x => x ≠ 0 ∧ x ≠ 1))
    (l : List (ZMod 23 × ℕ)) (hl : l.Nodup)
    (hmem : ∀ xb : ZMod 23 × ℕ, xb ∈ l ↔ xb.1 ∈ T ∧ xb.2 = 2)
    (p : ZMod 23) (hp : p ≠ 0) :
    -(4⁻¹ : ZMod 23) * p ^ 2 ∈ reach (l ++ [(p, 2)]) := by
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
  have hT0 : ∀ x ∈ T, x ≠ 0 ∧ x ≠ 1 := by
    intro x hx
    have := hTsub hx
    simpa using this
  set S : Finset ℕ := T.image log23 with hS_def
  have hS : S ∈ Finset.powersetCard 11 (Finset.Icc 1 21) := by
    rw [Finset.mem_powersetCard]
    constructor
    · intro v hv
      rw [hS_def, Finset.mem_image] at hv
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨h0, h1⟩ := hT0 x hx
      have := log23_range x h0 h1
      rw [Finset.mem_Icc]
      omega
    · rw [hS_def, Finset.card_image_of_injOn, hTcard]
      intro x hx y hy hxy
      have hx' := (log23_spec x (hT0 x hx).1).2
      have hy' := (log23_spec y (hT0 y hy).1).2
      rw [← hx', ← hy', hxy]
  set plog : ℕ := log23 p with hplog_def
  have hplog : plog < 22 := (log23_spec p hp).1
  have hpexp : (5 : ZMod 23) ^ plog = p := (log23_spec p hp).2
  set B : ℕ := (List.range 22).foldl
    (fun b v => if v ∈ S then b ||| rot22 b v ||| rot22 b (2 * v) else b)
    1 with hB_def
  have hall : (List.range 22).all (fun pl =>
      Nat.testBit (B ||| rot22 B pl ||| rot22 B (2 * pl))
        ((2 * pl + 7) % 22)) = true :=
    lemmaS_finite_R23 S hS
  have hmask : Nat.testBit (B ||| rot22 B plog ||| rot22 B (2 * plog))
      ((2 * plog + 7) % 22) = true :=
    List.all_eq_true.mp hall plog (List.mem_range.mpr hplog)
  have hBlt : B < 2 ^ 22 := by
    rw [hB_def, r23_fold_eq S (List.range 22) 1 (by norm_num)]
    generalize (List.range 22).filterMap _ = L
    induction L using List.reverseRecOn with
    | nil => norm_num
    | append_singleton l' xb _ =>
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact mstep_lt 22 _ xb.1 xb.2
  set Ls : List (ℕ × ℕ) := (List.range 22).filterMap
    (fun v => if v ∈ S then some (v, 2) else none) with hLs_def
  have hreachLs : reach (Ls.map fun vb => ((5 : ZMod 23) ^ vb.1, vb.2)) =
      maskSet 22 (5 : ZMod 23) B := by
    rw [reach_eq_maskSet 22 (5 : ZMod 23) g23_pow22 (by norm_num) Ls,
      hB_def, r23_fold_eq S (List.range 22) 1 (by norm_num), hLs_def]
  have hLs_mem : ∀ vb : ℕ × ℕ, vb ∈ Ls ↔ vb.1 ∈ S ∧ vb.2 = 2 := by
    intro vb
    rw [hLs_def, List.mem_filterMap]
    constructor
    · rintro ⟨v, _, hsome⟩
      by_cases hv : v ∈ S
      · rw [if_pos hv] at hsome
        cases hsome
        exact ⟨hv, rfl⟩
      · rw [if_neg hv] at hsome
        cases hsome
    · rintro ⟨hv1, hv2⟩
      refine ⟨vb.1, List.mem_range.mpr ?_, ?_⟩
      · have := hS
        rw [Finset.mem_powersetCard] at this
        have := this.1 hv1
        rw [Finset.mem_Icc] at this
        omega
      · rw [if_pos hv1]
        cases vb
        simp_all
  have hLs_nodup : Ls.Nodup := by
    rw [hLs_def]
    refine List.Nodup.filterMap ?_ (List.nodup_range)
    intro a a' b hb hb'
    by_cases ha : a ∈ S
    · by_cases ha' : a' ∈ S
      · rw [if_pos ha, Option.mem_def, Option.some_inj] at hb
        rw [if_pos ha', Option.mem_def, Option.some_inj] at hb'
        rw [← hb'] at hb
        exact (Prod.ext_iff.mp hb).1
      · rw [if_neg ha'] at hb'
        cases hb'
    · rw [if_neg ha] at hb
      cases hb
  have hmap_nodup :
      (Ls.map fun vb => ((5 : ZMod 23) ^ vb.1, vb.2)).Nodup := by
    refine List.Nodup.map_on ?_ hLs_nodup
    intro x hx y hy hxy
    have hx1 : x.1 < 22 := by
      have := (hLs_mem x).mp hx
      have h2 := hS
      rw [Finset.mem_powersetCard] at h2
      have := h2.1 this.1
      rw [Finset.mem_Icc] at this
      omega
    have hy1 : y.1 < 22 := by
      have := (hLs_mem y).mp hy
      have h2 := hS
      rw [Finset.mem_powersetCard] at h2
      have := h2.1 this.1
      rw [Finset.mem_Icc] at this
      omega
    obtain ⟨heq1, heq2⟩ := Prod.ext_iff.mp hxy
    have := g23_inj x.1 hx1 y.1 hy1 heq1
    exact Prod.ext this heq2
  have htoFin : l.toFinset =
      (Ls.map fun vb => ((5 : ZMod 23) ^ vb.1, vb.2)).toFinset := by
    ext xb
    rw [List.mem_toFinset, List.mem_toFinset, hmem, List.mem_map]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨(log23 xb.1, 2), ?_, ?_⟩
      · rw [hLs_mem]
        exact ⟨Finset.mem_image_of_mem _ hx1, rfl⟩
      · have := (log23_spec xb.1 (hT0 _ hx1).1).2
        cases xb
        simp_all
    · rintro ⟨⟨v, b2⟩, hvb, rfl⟩
      obtain ⟨hv1, hv2⟩ := (hLs_mem ⟨v, b2⟩).mp hvb
      dsimp only at hv1 hv2 ⊢
      subst hv2
      rw [hS_def, Finset.mem_image] at hv1
      obtain ⟨x, hx, hlog⟩ := hv1
      have hxe := (log23_spec x (hT0 x hx).1).2
      exact ⟨by rw [← hlog, hxe]; exact hx, rfl⟩
  have hperm : l.Perm (Ls.map fun vb => ((5 : ZMod 23) ^ vb.1, vb.2)) :=
    List.perm_of_nodup_nodup_toFinset_eq hl hmap_nodup htoFin
  rw [reach_append_single, reach_perm hperm, hreachLs, ← hpexp,
    ← maskSet_mstep 22 (5 : ZMod 23) g23_pow22 (by norm_num) hBlt plog 2,
    mstep_two 22 (by norm_num) hBlt plog, ← rot22_eq_rotg, ← rot22_eq_rotg]
  rw [mem_maskSet]
  refine ⟨(2 * plog + 7) % 22, Nat.mod_lt _ (by norm_num), hmask, ?_⟩
  rw [pow_mod_d 22 (5 : ZMod 23) g23_pow22, neg_inv4_23]
  ring

end R23Bridge

/-! ### The R = 11 bridge (Theorem A″, multiplicative form) -/

section R11Bridge

lemma g11_pow10 : (2 : ZMod 11) ^ 10 = 1 := by decide

lemma g11_inj : ∀ i, i < 10 → ∀ j, j < 10 →
    (2 : ZMod 11) ^ i = 2 ^ j → i = j := by decide

lemma neg_inv4_11 : -(4⁻¹ : ZMod 11) = 2 ^ 3 := by
  rw [ZMod.inv_eq_of_mul_eq_one 11 4 3 (by decide)]
  decide

/-- The guarded general-budget mask fold of `theoremA''_finite_R11` is
the `mstep` fold over the doubled-budget list. -/
lemma r11_fold_eq :
    ∀ (l : List (ℕ × ℕ)) (M : ℕ), M < 2 ^ 10 →
      l.foldl (fun b vm => if vm.2 = 0 then b else
          (List.range (2 * vm.2 + 1)).foldl
            (fun acc e => acc ||| rot10 b (vm.1 * e)) 0) M =
        (l.map fun vm => (vm.1, 2 * vm.2)).foldl
          (fun b vb => mstep 10 b vb.1 vb.2) M
  | [], _, _ => rfl
  | vm :: l, M, hM => by
      simp only [List.foldl_cons, List.map_cons]
      have hstep : (if vm.2 = 0 then M else
          (List.range (2 * vm.2 + 1)).foldl
            (fun acc e => acc ||| rot10 M (vm.1 * e)) 0) =
          mstep 10 M vm.1 (2 * vm.2) := by
        by_cases hm : vm.2 = 0
        · rw [if_pos hm, hm, Nat.mul_zero,
            mstep_zero 10 (by norm_num) hM]
        · rw [if_neg hm]
          show _ = (List.range (2 * vm.2 + 1)).foldl
            (fun acc e => acc ||| rotg 10 M (vm.1 * e)) 0
          simp only [rot10_eq_rotg]
      rw [hstep]
      exact r11_fold_eq l _ (mstep_lt 10 M vm.1 (2 * vm.2))

set_option maxHeartbeats 1600000 in
/-- **Theorem A″, multiplicative form** (the discrete-log bridge
applied to `theoremA''_finite_R11`). `cᵢ` is the capped multiplicity
of the unit class `i` among the prime factors of `a = (p+11)/4` (caps
by order: classes `2, 8, 7, 6` cap 5, classes `4, 5, 9, 3` cap 3,
class `10` cap 1); `3 ∣ a` forces `c₃ ≥ 1`; consistency forces
`p = 4·∏ classes^mult`. Then the target `−4⁻¹p²` is reachable **iff**
the configuration avoids both Theorem A″ failure shapes: (a) all
classes quadratic residues, and (b) the three exact budget patterns
over classes 2 and 6 with their paired values of `p`. -/
theorem theoremA''_finite_R11_mult :
    ∀ (c2 c8 c7 c6 : Fin 6) (c4 c5 c9 c3 : Fin 4) (c10 : Fin 2),
      1 ≤ c3.val →
      ∀ p : ZMod 11,
      p = 4 * (2 ^ c2.val * 4 ^ c4.val * 8 ^ c8.val * 5 ^ c5.val *
        10 ^ c10.val * 9 ^ c9.val * 7 ^ c7.val * 3 ^ c3.val *
        6 ^ c6.val) →
      (-(4⁻¹ : ZMod 11) * p ^ 2 ∈
          reach [((2 : ZMod 11), 2 * c2.val), (4, 2 * c4.val),
            (8, 2 * c8.val), (5, 2 * c5.val), (10, 2 * c10.val),
            (9, 2 * c9.val), (7, 2 * c7.val), (3, 2 * c3.val),
            (6, 2 * c6.val), (p, 2)]
        ↔ ¬((c2 = 0 ∧ c8 = 0 ∧ c10 = 0 ∧ c7 = 0 ∧ c6 = 0) ∨
            (c3 = 1 ∧ c4 = 0 ∧ c5 = 0 ∧ c9 = 0 ∧ c8 = 0 ∧ c10 = 0 ∧
              c7 = 0 ∧
              ((c2 = 1 ∧ c6 = 0 ∧ p = 2) ∨
               (c2 = 0 ∧ c6 = 1 ∧ p = 6) ∨
               (c2 = 1 ∧ c6 = 1 ∧ p = 1))))) := by
  intro c2 c8 c7 c6 c4 c5 c9 c3 c10 hc3 p hpdef
  set alog : ℕ := (c2.val + 2 * c4.val + 3 * c8.val + 4 * c5.val +
    5 * c10.val + 6 * c9.val + 7 * c7.val + 8 * c3.val +
    9 * c6.val) % 10 with halog_def
  set plog : ℕ := (alog + 2) % 10 with hplog_def
  have hplog : plog < 10 := by omega
  set B : ℕ := [(1, c2.val), (2, c4.val), (3, c8.val), (4, c5.val),
    (5, c10.val), (6, c9.val), (7, c7.val), (8, c3.val),
    (9, c6.val)].foldl
      (fun b vm => if vm.2 = 0 then b else
        (List.range (2 * vm.2 + 1)).foldl
          (fun acc e => acc ||| rot10 b (vm.1 * e)) 0) 1 with hB_def
  have hmask : (Nat.testBit (B ||| rot10 B plog ||| rot10 B (2 * plog))
      ((5 + alog + plog) % 10)
    == !(((c2 == 0) && (c8 == 0) && (c10 == 0) && (c7 == 0) &&
           (c6 == 0)) ||
         ((c3 == 1) && (c4 == 0) && (c5 == 0) && (c9 == 0) &&
           (c8 == 0) && (c10 == 0) && (c7 == 0) &&
           (((c2 == 1) && (c6 == 0) && (plog == 1)) ||
            ((c2 == 0) && (c6 == 1) && (plog == 9)) ||
            ((c2 == 1) && (c6 == 1) && (plog == 0)))))) = true :=
    theoremA''_finite_R11 c2 c8 c7 c6 c4 c5 c9 c3 c10 hc3
  rw [beq_iff_eq] at hmask
  -- `p` is the power of 2 the consistency relation dictates
  have hpexp : (2 : ZMod 11) ^ plog = p := by
    have h1 : (2 : ZMod 11) ^ plog = 2 ^ (alog + 2) := by
      rw [hplog_def]
      exact pow_mod_d 10 _ g11_pow10 _
    have h2 : (2 : ZMod 11) ^ alog =
        2 ^ (c2.val + 2 * c4.val + 3 * c8.val + 4 * c5.val +
          5 * c10.val + 6 * c9.val + 7 * c7.val + 8 * c3.val +
          9 * c6.val) := by
      rw [halog_def]
      exact pow_mod_d 10 _ g11_pow10 _
    rw [h1, pow_add, h2, hpdef,
      show (4 : ZMod 11) = 2 ^ 2 from by decide,
      show (8 : ZMod 11) = 2 ^ 3 from by decide,
      show (5 : ZMod 11) = 2 ^ 4 from by decide,
      show (10 : ZMod 11) = 2 ^ 5 from by decide,
      show (9 : ZMod 11) = 2 ^ 6 from by decide,
      show (3 : ZMod 11) = 2 ^ 8 from by decide,
      show (6 : ZMod 11) = 2 ^ 9 from by decide,
      show (7 : ZMod 11) = 2 ^ 7 from by decide]
    simp only [← pow_mul]
    ring
  have hBlt : B < 2 ^ 10 := by
    rw [hB_def, r11_fold_eq _ 1 (by norm_num)]
    generalize (List.map _ _ : List (ℕ × ℕ)) = L
    induction L using List.reverseRecOn with
    | nil => norm_num
    | append_singleton l' xb _ =>
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact mstep_lt 10 _ xb.1 xb.2
  -- the configuration list is the mapped (log, budget) list
  have hLc : ([((2 : ZMod 11), 2 * c2.val), (4, 2 * c4.val),
      (8, 2 * c8.val), (5, 2 * c5.val), (10, 2 * c10.val),
      (9, 2 * c9.val), (7, 2 * c7.val), (3, 2 * c3.val),
      (6, 2 * c6.val)] : List (ZMod 11 × ℕ)) =
      ([(1, c2.val), (2, c4.val), (3, c8.val), (4, c5.val),
        (5, c10.val), (6, c9.val), (7, c7.val), (8, c3.val),
        (9, c6.val)].map fun vm => (vm.1, 2 * vm.2)).map
        (fun vb => ((2 : ZMod 11) ^ vb.1, vb.2)) := by
    simp only [List.map_cons, List.map_nil, pow_one,
      show (2 : ZMod 11) ^ 2 = 4 from by decide,
      show (2 : ZMod 11) ^ 3 = 8 from by decide,
      show (2 : ZMod 11) ^ 4 = 5 from by decide,
      show (2 : ZMod 11) ^ 5 = 10 from by decide,
      show (2 : ZMod 11) ^ 6 = 9 from by decide,
      show (2 : ZMod 11) ^ 7 = 7 from by decide,
      show (2 : ZMod 11) ^ 8 = 3 from by decide,
      show (2 : ZMod 11) ^ 9 = 6 from by decide]
  have hreach : reach ([((2 : ZMod 11), 2 * c2.val), (4, 2 * c4.val),
      (8, 2 * c8.val), (5, 2 * c5.val), (10, 2 * c10.val),
      (9, 2 * c9.val), (7, 2 * c7.val), (3, 2 * c3.val),
      (6, 2 * c6.val)] : List (ZMod 11 × ℕ)) =
      maskSet 10 (2 : ZMod 11) B := by
    rw [hLc, reach_eq_maskSet 10 (2 : ZMod 11) g11_pow10 (by norm_num),
      hB_def, r11_fold_eq _ 1 (by norm_num)]
  -- the target class in log coordinates
  have htarget : (2 : ZMod 11) ^ ((5 + alog + plog) % 10) =
      -(4⁻¹ : ZMod 11) * p ^ 2 := by
    have hexp : (5 + alog + plog) % 10 = (3 + 2 * plog) % 10 := by omega
    rw [hexp, pow_mod_d 10 _ g11_pow10, neg_inv4_11, ← hpexp]
    ring
  -- membership ↔ the target bit
  have hmem_iff :
      (-(4⁻¹ : ZMod 11) * p ^ 2 ∈
        maskSet 10 (2 : ZMod 11)
          (B ||| rot10 B plog ||| rot10 B (2 * plog))) ↔
      Nat.testBit (B ||| rot10 B plog ||| rot10 B (2 * plog))
        ((5 + alog + plog) % 10) = true := by
    constructor
    · intro hmem
      rw [mem_maskSet] at hmem
      obtain ⟨i, hi, hbit, hpow⟩ := hmem
      have hieq : i = (5 + alog + plog) % 10 :=
        g11_inj i hi _ (by omega) (by rw [hpow, htarget])
      rwa [hieq] at hbit
    · intro hbit
      rw [mem_maskSet]
      exact ⟨(5 + alog + plog) % 10, by omega, hbit, htarget⟩
  -- the paired-p dictionary
  have hp2 : plog = 1 ↔ p = 2 := by
    constructor
    · intro h; rw [← hpexp, h]; decide
    · intro h
      exact g11_inj plog hplog 1 (by norm_num)
        (by rw [hpexp, h]; decide)
  have hp6 : plog = 9 ↔ p = 6 := by
    constructor
    · intro h; rw [← hpexp, h]; decide
    · intro h
      exact g11_inj plog hplog 9 (by norm_num)
        (by rw [hpexp, h]; decide)
  have hp1 : plog = 0 ↔ p = 1 := by
    constructor
    · intro h; rw [← hpexp, h]; decide
    · intro h
      exact g11_inj plog hplog 0 (by norm_num)
        (by rw [hpexp, h]; decide)
  -- assemble
  rw [show ([((2 : ZMod 11), 2 * c2.val), (4, 2 * c4.val),
      (8, 2 * c8.val), (5, 2 * c5.val), (10, 2 * c10.val),
      (9, 2 * c9.val), (7, 2 * c7.val), (3, 2 * c3.val),
      (6, 2 * c6.val), (p, 2)] : List (ZMod 11 × ℕ)) =
      [((2 : ZMod 11), 2 * c2.val), (4, 2 * c4.val),
      (8, 2 * c8.val), (5, 2 * c5.val), (10, 2 * c10.val),
      (9, 2 * c9.val), (7, 2 * c7.val), (3, 2 * c3.val),
      (6, 2 * c6.val)] ++ [(p, 2)] from rfl,
    reach_append_single, hreach, ← hpexp,
    ← maskSet_mstep 10 (2 : ZMod 11) g11_pow10 (by norm_num) hBlt plog 2,
    mstep_two 10 (by norm_num) hBlt plog, ← rot10_eq_rotg,
    ← rot10_eq_rotg, hpexp, hmem_iff, hmask]
  have hbool : ((((c2 == 0) && (c8 == 0) && (c10 == 0) && (c7 == 0) &&
        (c6 == 0)) ||
      ((c3 == 1) && (c4 == 0) && (c5 == 0) && (c9 == 0) &&
        (c8 == 0) && (c10 == 0) && (c7 == 0) &&
        (((c2 == 1) && (c6 == 0) && (plog == 1)) ||
         ((c2 == 0) && (c6 == 1) && (plog == 9)) ||
         ((c2 == 1) && (c6 == 1) && (plog == 0))))) = true) ↔
      ((c2 = 0 ∧ c8 = 0 ∧ c10 = 0 ∧ c7 = 0 ∧ c6 = 0) ∨
        (c3 = 1 ∧ c4 = 0 ∧ c5 = 0 ∧ c9 = 0 ∧ c8 = 0 ∧ c10 = 0 ∧
          c7 = 0 ∧
          ((c2 = 1 ∧ c6 = 0 ∧ p = 2) ∨
           (c2 = 0 ∧ c6 = 1 ∧ p = 6) ∨
           (c2 = 1 ∧ c6 = 1 ∧ p = 1)))) := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, hp2, hp6,
      hp1, and_assoc, or_assoc]
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
  exact not_congr hbool

end R11Bridge

end ErdosStraus

-- Audit. The bridge layer itself is symbolic (standard axioms only);
-- the two `_mult` theorems inherit exactly the mask theorems' single
-- `native_decide` axiom each — the bridge adds no computational trust.
#print axioms ErdosStraus.maskSet_rotg
#print axioms ErdosStraus.maskSet_mstep
#print axioms ErdosStraus.reach_eq_maskSet
#print axioms ErdosStraus.reach_perm
#print axioms ErdosStraus.lemmaS_finite_R19_mult
#print axioms ErdosStraus.lemmaS_finite_R23_mult
#print axioms ErdosStraus.theoremA''_finite_R11_mult
