/-
Lemma S at R = 31, by *verified dynamic programming*.

The direct enumeration is out of reach for the evaluator here:
C(29,15) = 77,558,760 supports. The Python verifier
(`theory.verify_support_bound_dp`) folds the supports into 3,001
reachability-mask states. This file formalizes that reduction: a DP
over (mask, capped support count) states, one round per class
`v = 1 … 29`, where each round carries every state and adds its
extension by `v` (sorting and merging equal masks with `max` count —
the sort is only compaction and needs no correctness proof).

Soundness needs exactly two properties of a round — every state is
carried (`round_carry`) and every extension is present (`round_ext`)
— plus a prefix induction (`dp_sound_aux`): after processing classes
`1 … j`, every support `S ⊆ {1..j}` has a state whose mask is the
base mask of `S` and whose count is at least `min |S| 15`. The final
check (`dp_check`, the only `native_decide`) verifies that every
state with count ≥ 15 hits every target. Together these prove the
R = 31 support-bound in the same mask form as `lemmaS_finite_R19` —
with the 77.5M-support space never enumerated.

Discrete-log data (primitive root 3 mod 31): `log₃ 4⁻¹ = 12`,
`log₃(−1) = 15`, so the target for class `plog` of `p` is bit
`(15 + 2·plog + 12) % 30 = (2·plog + 27) % 30`.
-/
import Mathlib.Tactic

namespace ErdosStraus

/-- Cyclic rotation of a 30-bit mask: discrete-log coordinates for
`(ℤ/31)ˣ` (primitive root `g = 3`; bit `i` is the class `3^i mod 31`). -/
def rot30 (m s : ℕ) : ℕ :=
  ((m <<< (s % 30)) ||| (m >>> (30 - s % 30))) &&& (2 ^ 30 - 1)

namespace R31

/-- Extending a base mask by a class of log `v` (exponent budget 2). -/
def ext (m v : ℕ) : ℕ := m ||| rot30 m v ||| rot30 m (2 * v)

/-- Merge adjacent equal-mask entries, keeping the larger count. Only
adjacent entries merge, so no sortedness assumption is ever needed for
correctness — sorting is used purely to compact the state list. -/
def dedupMax : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      if x.1 = y.1 then dedupMax ((x.1, max x.2 y.2) :: t)
      else x :: dedupMax (y :: t)
  termination_by l => l.length

/-- Every input entry is dominated by an output entry with the same
mask and at least its count. -/
lemma dedupMax_dominates :
    ∀ (l : List (ℕ × ℕ)), ∀ x ∈ l,
      ∃ y ∈ dedupMax l, y.1 = x.1 ∧ x.2 ≤ y.2 := by
  intro l
  induction l using dedupMax.induct with
  | case1 =>
      intro x hx
      cases hx
  | case2 z =>
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨x, by simp [dedupMax], rfl, le_rfl⟩
  | case3 a b t heq ih =>
      intro x hx
      rw [show dedupMax (a :: b :: t) = dedupMax ((a.1, max a.2 b.2) :: t)
        from by rw [dedupMax]; simp [heq]]
      rcases List.mem_cons.mp hx with rfl | hx'
      · obtain ⟨y, hy, hy1, hy2⟩ :=
          ih (x.1, max x.2 b.2) List.mem_cons_self
        exact ⟨y, hy, hy1, le_trans (le_max_left _ _) hy2⟩
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · obtain ⟨y, hy, hy1, hy2⟩ :=
            ih (a.1, max a.2 x.2) List.mem_cons_self
          exact ⟨y, hy, by rw [hy1]; exact heq,
            le_trans (le_max_right _ _) hy2⟩
        · obtain ⟨y, hy, hy1, hy2⟩ :=
            ih x (List.mem_cons_of_mem _ hx'')
          exact ⟨y, hy, hy1, hy2⟩
  | case4 a b t hne ih =>
      intro x hx
      rw [show dedupMax (a :: b :: t) = a :: dedupMax (b :: t)
        from by rw [dedupMax]; simp [hne]]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨x, List.mem_cons_self, rfl, le_rfl⟩
      · obtain ⟨y, hy, hy1, hy2⟩ := ih x hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hy1, hy2⟩

/-- One DP round: carry all states and add the extension of each by
class `v`, then compact. -/
def round (states : List (ℕ × ℕ)) (v : ℕ) : List (ℕ × ℕ) :=
  dedupMax ((states ++ states.map fun mc : ℕ × ℕ =>
    (ext mc.1 v, min (mc.2 + 1) 15)).mergeSort (fun a b => a.1 ≤ b.1))

lemma mem_round_of_mem {states : List (ℕ × ℕ)} {v : ℕ}
    {x : ℕ × ℕ} (hx : x ∈ states ++ states.map fun mc : ℕ × ℕ =>
      (ext mc.1 v, min (mc.2 + 1) 15)) :
    ∃ y ∈ round states v, y.1 = x.1 ∧ x.2 ≤ y.2 := by
  apply dedupMax_dominates
  exact ((List.mergeSort_perm _ _).mem_iff).mpr hx

/-- Every state is carried through a round. -/
lemma round_carry {states : List (ℕ × ℕ)} {v : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ states) :
    ∃ y ∈ round states v, y.1 = x.1 ∧ x.2 ≤ y.2 :=
  mem_round_of_mem (List.mem_append_left _ hx)

/-- Every extension is present after a round. -/
lemma round_ext {states : List (ℕ × ℕ)} {v : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ states) :
    ∃ y ∈ round states v, y.1 = ext x.1 v ∧ min (x.2 + 1) 15 ≤ y.2 :=
  mem_round_of_mem (List.mem_append_right _
    (List.mem_map.mpr ⟨x, hx, rfl⟩))

/-- The DP: process classes `1 … 29` from the empty-support state. -/
def dp : List (ℕ × ℕ) := (List.range' 1 29).foldl round [(1, 0)]

/-- Does a mask hit the target for every class of `p`? -/
def targetsOk (m : ℕ) : Bool :=
  (List.range 30).all fun pl =>
    Nat.testBit (m ||| rot30 m pl ||| rot30 m (2 * pl))
      ((2 * pl + 27) % 30)

/-- The verified final check: every DP state realized by ≥ 15 classes
hits every target. This is the only computational step. -/
lemma dp_check :
    (dp.all fun mc => decide (mc.2 < 15) || targetsOk mc.1) = true := by
  native_decide

/-- Skipped segments leave the base fold unchanged. -/
lemma baseFold_skip (S : Finset ℕ) :
    ∀ (l : List ℕ) (M : ℕ), (∀ v ∈ l, v ∉ S) →
      l.foldl (fun b v => if v ∈ S then ext b v else b) M = M
  | [], _, _ => rfl
  | v :: t, M, h => by
      rw [List.foldl_cons, if_neg (h v List.mem_cons_self)]
      exact baseFold_skip S t M fun w hw => h w (List.mem_cons_of_mem v hw)

/-- The base fold only depends on membership along the fold list. -/
lemma baseFold_congr (S S' : Finset ℕ) :
    ∀ (l : List ℕ) (M : ℕ), (∀ v ∈ l, (v ∈ S ↔ v ∈ S')) →
      l.foldl (fun b v => if v ∈ S then ext b v else b) M =
        l.foldl (fun b v => if v ∈ S' then ext b v else b) M
  | [], _, _ => rfl
  | v :: t, M, h => by
      have hv := h v List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons]
      by_cases hvS : v ∈ S
      · rw [if_pos hvS, if_pos (hv.mp hvS)]
        exact baseFold_congr S S' t _
          fun w hw => h w (List.mem_cons_of_mem v hw)
      · rw [if_neg hvS, if_neg fun hc => hvS (hv.mpr hc)]
        exact baseFold_congr S S' t M
          fun w hw => h w (List.mem_cons_of_mem v hw)

/-- **DP soundness.** After processing classes `1 … j`, every support
`S ⊆ {1..j}` is represented: some state has exactly the base mask of
`S` and count at least `min |S| 15`. -/
lemma dp_sound_aux :
    ∀ (j : ℕ), ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 j →
      ∃ mc ∈ (List.range' 1 j).foldl round [(1, 0)],
        mc.1 = (List.range (j + 1)).foldl
          (fun b v => if v ∈ S then ext b v else b) 1 ∧
        min S.card 15 ≤ mc.2 := by
  intro j
  induction j with
  | zero =>
      intro S hS
      have hSempty : S = ∅ := by
        rw [← Finset.subset_empty]
        rwa [show Finset.Icc 1 0 = ∅ from Finset.Icc_eq_empty (by omega)]
          at hS
      subst hSempty
      refine ⟨(1, 0), by simp [List.range'], ?_, by simp⟩
      rw [baseFold_skip ∅ _ _ (by simp)]
  | succ j ih =>
      intro S hS
      have hconcat : List.range' 1 (j + 1) =
          List.range' 1 j ++ [1 + j] := by
        have := List.range'_concat (s := 1) (n := j) (step := 1)
        simpa using this
      rw [hconcat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hmem : (j + 1) ∈ S
      · -- the new class is used: extend the erased support's state
        set S' : Finset ℕ := S.erase (j + 1) with hS'_def
        have hS'sub : S' ⊆ Finset.Icc 1 j := by
          intro x hx
          rw [hS'_def, Finset.mem_erase] at hx
          have := hS hx.2
          rw [Finset.mem_Icc] at this ⊢
          omega
        obtain ⟨mc', hmc'mem, hmask', hcnt'⟩ := ih S' hS'sub
        obtain ⟨y, hymem, hy1, hy2⟩ := round_ext (v := 1 + j) hmc'mem
        have hsplit : (List.range (j + 1 + 1)).foldl
            (fun b v => if v ∈ S then ext b v else b) 1 =
            ext ((List.range (j + 1)).foldl
              (fun b v => if v ∈ S then ext b v else b) 1) (j + 1) := by
          conv_lhs => rw [List.range_succ]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
            if_pos hmem]
        have hagree : ∀ v ∈ List.range (j + 1), (v ∈ S' ↔ v ∈ S) := by
          intro v hv
          rw [List.mem_range] at hv
          rw [hS'_def, Finset.mem_erase]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨by omega, h⟩
        refine ⟨y, hymem, ?_, ?_⟩
        · rw [hy1, hmask', baseFold_congr S' S _ 1 hagree,
            show (1 : ℕ) + j = j + 1 from Nat.add_comm 1 j, hsplit]
        · have hcard : S'.card = S.card - 1 := by
            rw [hS'_def]
            exact Finset.card_erase_of_mem hmem
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨_, hmem⟩
          omega
      · -- the new class is unused: carry the state
        have hSsub : S ⊆ Finset.Icc 1 j := by
          intro x hx
          have := hS hx
          rw [Finset.mem_Icc] at this ⊢
          have : x ≠ j + 1 := fun h => hmem (h ▸ hx)
          omega
        obtain ⟨mc', hmc'mem, hmask', hcnt'⟩ := ih S hSsub
        obtain ⟨y, hymem, hy1, hy2⟩ := round_carry (v := 1 + j) hmc'mem
        have hsplit : (List.range (j + 1 + 1)).foldl
            (fun b v => if v ∈ S then ext b v else b) 1 =
            (List.range (j + 1)).foldl
              (fun b v => if v ∈ S then ext b v else b) 1 := by
          conv_lhs => rw [List.range_succ]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
            if_neg hmem]
        refine ⟨y, hymem, ?_, by omega⟩
        rw [hy1, hmask', hsplit]

/-- **Lemma S, finite verification at R = 31** — the same mask-form
statement as `lemmaS_finite_R19` / `lemmaS_finite_R23`, but proved by
verified dynamic programming instead of direct enumeration: the
C(29,15) = 77,558,760 supports are never enumerated; the DP soundness
induction covers them all through 3,001 states. -/
theorem lemmaS_finite_R31 :
    ∀ S ∈ Finset.powersetCard 15 (Finset.Icc 1 29),
      ∀ plog : ℕ, plog < 30 →
        (let base := (List.range 30).foldl
            (fun b v => if v ∈ S then b ||| rot30 b v ||| rot30 b (2 * v)
             else b) 1
         Nat.testBit (base ||| rot30 base plog ||| rot30 base (2 * plog))
           ((2 * plog + 27) % 30)) = true := by
  intro S hS plog hplog
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  obtain ⟨mc, hmem, hmask, hcnt⟩ := dp_sound_aux 29 S hsub
  have hcnt15 : 15 ≤ mc.2 := by
    rw [hcard] at hcnt
    simpa using hcnt
  have hchk := dp_check
  rw [List.all_eq_true] at hchk
  have hentry := hchk mc hmem
  rw [Bool.or_eq_true, decide_eq_true_iff] at hentry
  rcases hentry with h | h
  · omega
  · rw [targetsOk, List.all_eq_true] at h
    have hbit := h plog (List.mem_range.mpr hplog)
    show Nat.testBit _ _ = true
    have hbase : (List.range 30).foldl
        (fun b v => if v ∈ S then b ||| rot30 b v ||| rot30 b (2 * v)
         else b) 1 = mc.1 := hmask.symm
    rw [hbase]
    exact hbit

end R31

end ErdosStraus

-- Audit. Everything symbolic except the single `native_decide` of
-- `dp_check` (3,001 states × 30 targets), which the main theorem
-- inherits; the DP soundness induction is standard axioms only.
#print axioms ErdosStraus.R31.dedupMax_dominates
#print axioms ErdosStraus.R31.dp_sound_aux
#print axioms ErdosStraus.R31.lemmaS_finite_R31
