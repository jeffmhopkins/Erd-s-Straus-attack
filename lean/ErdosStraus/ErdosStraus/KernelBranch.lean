/-
The kernel branch of the branch classification: the paper's
Theorem 4.8 (`thm:Mkernel`, "kernel branch; lossless reduction") and
Proposition 4.12 (`prop:betavac`, β-vacuity).

Setting. At exponent budget `2` per class a *support*
`S ⊆ G \ {0}` (`G = ZMod d` in the application) has *reach*
`M(S) = ∑_{v ∈ S} {0, v, 2v}` — the same bounded subset-sum set as in
`TheoremS.lean`, here packaged as `reach2` (`reach2_zmod` is the
bridge to the sum form Theorem S is stated in). `S` *fails* for a
target `t` if `t ∉ M(S)`, and is *maximal* if moreover every
one-element extension `S ∪ {w}` (`w ≠ 0`, `w ∉ S`) attains `t`.

Theorem 4.8, in three parts, with `H = Stab(M(S))` the stabilizer of
the reach and `φ` any hom with kernel exactly `H` (the quotient
`φ_H : ZMod d → ZMod d̄` of the paper; `exists_addStab_quotient`
builds it):

* (i) `target_notMem_reach2_add_addStab`, `projected_target_ne_zero`,
  `zero_notMem_projected_support`, `projected_failing`: `t ∉ M(S) + H`,
  and `T̄ = φ(S \ H)` is a support of nonzero classes failing for
  `t̄ = φ(t) ≠ 0` downstairs.
* (ii) `addStab_erase_zero_subset_of_maximal`: maximality forces
  `H \ {0} ⊆ S` (for `w ∈ H` the summand `A_w ⊆ H` stabilizes `M(S)`,
  so the extension does not grow the reach).
* (iii) `support_subset_container`: `S ⊆ (H \ {0}) ∪ φ⁻¹(T̄)`.

The size bookkeeping of the theorem's last paragraph is
`card_container_le` (`#((H \ {0}) ∪ φ⁻¹(T̄)) ≤ (h − 1) + h·#T̄`) and
`kernel_branch_card_bound` (one reduction step, with Theorem S applied
downstairs in both parities of `d̄`, giving `#S ≤ d/2 − 1`; the
`d̄ = 2` edge case is automatic, Theorem S forcing `T̄ = ∅` there).

Proposition 4.12 is `betaVacuity` (plus `betaVacuity_aperiodic`, the
"in particular" clause): a Kneser-critical deletion step of punctured
type puts the deleted class in `Stab(M(S))`, so at an aperiodic
maximal failing support no critical deletion step is of punctured
type.

Everything here is symbolic: standard axioms only, no `native_decide`.
-/
import ErdosStraus.TheoremS

namespace ErdosStraus

open Finset
open scoped Pointwise

/-! ### The budget-2 reach -/

section Reach

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The budget-2 summand at a class `v`: `A_v = {0, v, 2v}`. -/
def budget2 (v : G) : Finset G := {0, v, v + v}

/-- The budget-2 **reach** of a support: `M(S) = ∑_{v ∈ S} {0, v, 2v}`,
the bounded subset-sum set of `TheoremS.lean` (see `reach2_zmod`). -/
def reach2 (S : Finset G) : Finset G := ∑ v ∈ S, budget2 v

/-- `S` **fails** for the target `t` if `t` is not reached. -/
def Failing (S : Finset G) (t : G) : Prop := t ∉ reach2 S

/-- `S` is a **maximal** failing support for `t`: it fails, and every
one-element extension by a nonzero class attains `t`. -/
def MaximalFailing (S : Finset G) (t : G) : Prop :=
  Failing S t ∧ ∀ w : G, w ≠ 0 → w ∉ S → t ∈ reach2 (insert w S)

@[simp] lemma zero_mem_budget2 (v : G) : (0 : G) ∈ budget2 v := by
  simp [budget2]

@[simp] lemma budget2_zero : budget2 (0 : G) = 0 := by
  simp [budget2, Finset.singleton_zero]

@[simp] lemma reach2_empty : reach2 (∅ : Finset G) = 0 := by
  simp [reach2]

lemma reach2_insert {w : G} {S : Finset G} (hw : w ∉ S) :
    reach2 (insert w S) = budget2 w + reach2 S := by
  simp [reach2, Finset.sum_insert hw]

@[simp] lemma zero_mem_reach2 (S : Finset G) : (0 : G) ∈ reach2 S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reach2]
  | insert w S hw ih =>
      rw [reach2_insert hw]
      have := Finset.add_mem_add (zero_mem_budget2 w) ih
      simpa using this

lemma reach2_nonempty (S : Finset G) : (reach2 S).Nonempty :=
  ⟨0, zero_mem_reach2 S⟩

/-- The reach in `ZMod d` is the bounded subset-sum set Theorem S
(`theoremS_support_bound`, `theoremS_support_bound_odd`) is stated for. -/
lemma reach2_zmod {d : ℕ} (S : Finset (ZMod d)) :
    reach2 S = ∑ v ∈ S, ({0, v, 2 * v} : Finset (ZMod d)) :=
  Finset.sum_congr rfl fun v _ => by rw [budget2, two_mul]

/-! ### The stabilizer of the reach -/

/-- The stabilizer of a nonempty finset is closed under addition. -/
lemma addStab_add_mem {s : Finset G} {a b : G} (ha : a ∈ s.addStab)
    (hb : b ∈ s.addStab) : a + b ∈ s.addStab := by
  rw [← Finset.addStab_add_addStab s]
  exact Finset.add_mem_add ha hb

/-- The stabilizer of a nonempty finset is closed under negation. -/
lemma addStab_neg_mem {s : Finset G} (hs : s.Nonempty) {a : G}
    (ha : a ∈ s.addStab) : -a ∈ s.addStab := by
  rw [Finset.mem_addStab hs]
  have ha' := (Finset.mem_addStab hs).mp ha
  calc (-a) +ᵥ s = (-a) +ᵥ (a +ᵥ s) := by rw [ha']
    _ = ((-a) + a) +ᵥ s := (add_vadd _ _ _).symm
    _ = s := by rw [neg_add_cancel, zero_vadd]

/-- `M(S)` absorbs its own stabilizer, so `H ⊆ M(S)` (as `0 ∈ M(S)`). -/
lemma addStab_subset_reach2 (S : Finset G) :
    (reach2 S).addStab ⊆ reach2 S := by
  intro x hx
  have h := Finset.add_mem_add (zero_mem_reach2 S) hx
  rw [zero_add, Finset.add_addStab] at h
  exact h

/-- The budget-2 summand at a stabilizer class lies in the stabilizer. -/
lemma budget2_subset_addStab {S : Finset G} {w : G}
    (hw : w ∈ (reach2 S).addStab) : budget2 w ⊆ (reach2 S).addStab := by
  intro x hx
  simp only [budget2, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact (reach2_nonempty S).zero_mem_addStab
  · exact hw
  · exact addStab_add_mem hw hw

/-! ### Theorem 4.8(i): the projected support fails downstairs -/

/-- **Theorem 4.8, first clause**: a failing target is missed by the
whole `H`-saturation `M(S) + H` of the reach. -/
theorem target_notMem_reach2_add_addStab {S : Finset G} {t : G}
    (hfail : Failing S t) : t ∉ reach2 S + (reach2 S).addStab := by
  rw [Finset.add_addStab]
  exact hfail

variable {G' : Type*} [AddCommGroup G'] [DecidableEq G']

/-- A hom pushes the reach forward to the (possibly colliding) sum of
the projected summands. -/
lemma image_reach2 (φ : G →+ G') (S : Finset G) :
    (reach2 S).image φ = ∑ v ∈ S, budget2 (φ v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reach2, budget2, Finset.singleton_zero]
  | insert w S hw ih =>
      rw [reach2_insert hw, Finset.image_add, ih, Finset.sum_insert hw]
      congr 1
      simp [budget2, Finset.image_insert, map_add]

/-- Collisions only enlarge the reach: the reach of an image is
contained in the sum of the projected summands (Lemma 4.1
monotonicity, in the form Theorem 4.8 uses). -/
lemma reach2_image_subset (f : G → G') (U : Finset G) :
    reach2 (U.image f) ⊆ ∑ v ∈ U, budget2 (f v) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert w U hw ih =>
      rw [Finset.image_insert, Finset.sum_insert hw]
      by_cases hmem : f w ∈ U.image f
      · rw [Finset.insert_eq_self.mpr hmem]
        refine ih.trans ?_
        intro x hx
        have := Finset.add_mem_add (zero_mem_budget2 (f w)) hx
        simpa using this
      · rw [reach2_insert hmem]
        exact Finset.add_subset_add_left ih

/-- Classes of `S` inside the kernel contribute nothing downstairs. -/
lemma sum_budget2_sdiff (φ : G →+ G') (S H : Finset G)
    (hH : ∀ v ∈ H, φ v = 0) :
    ∑ v ∈ S, budget2 (φ v) = ∑ v ∈ S \ H, budget2 (φ v) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => v ∈ H)
    (fun v => budget2 (φ v))]
  have h1 : ∑ v ∈ S.filter (fun v => v ∈ H), budget2 (φ v) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [hH v hv.2, budget2_zero]
  rw [h1, zero_add, Finset.sdiff_eq_filter]

variable {S : Finset G} {t : G}

/-- **Theorem 4.8(i)**, target clause: the projected target is nonzero
(`H ⊆ M(S)`, so a target in `H` would be reached). -/
theorem projected_target_ne_zero (φ : G →+ G') (hfail : Failing S t)
    (hker : ∀ x : G, φ x = 0 ↔ x ∈ (reach2 S).addStab) : φ t ≠ 0 := by
  intro h0
  exact hfail (addStab_subset_reach2 S ((hker t).mp h0))

/-- **Theorem 4.8(i)**, support clause: the projected support consists
of nonzero classes. -/
theorem zero_notMem_projected_support (φ : G →+ G')
    (hker : ∀ x : G, φ x = 0 ↔ x ∈ (reach2 S).addStab) :
    (0 : G') ∉ (S \ (reach2 S).addStab).image φ := by
  intro h0
  rw [Finset.mem_image] at h0
  obtain ⟨v, hv, hv0⟩ := h0
  rw [Finset.mem_sdiff] at hv
  exact hv.2 ((hker v).mp hv0)

/-- **Theorem 4.8(i)**, main clause: the image of `S \ H` in the
quotient is a failing support for the projected target — the reduction
is lossless. -/
theorem projected_failing (φ : G →+ G') (hfail : Failing S t)
    (hker : ∀ x : G, φ x = 0 ↔ x ∈ (reach2 S).addStab) :
    Failing ((S \ (reach2 S).addStab).image φ) (φ t) := by
  classical
  intro hmem
  -- downstairs reach ⊆ pushforward of the reach upstairs
  have h1 := reach2_image_subset (φ : G → G') (S \ (reach2 S).addStab)
  have h2 : ∑ v ∈ S \ (reach2 S).addStab, budget2 (φ v)
      = (reach2 S).image φ := by
    rw [image_reach2 φ S]
    exact (sum_budget2_sdiff φ S (reach2 S).addStab
      (fun v hv => (hker v).mpr hv)).symm
  have h3 : φ t ∈ (reach2 S).image φ := h2 ▸ h1 hmem
  rw [Finset.mem_image] at h3
  obtain ⟨m, hm, hmt⟩ := h3
  -- the difference lies in the kernel `H`, and `M(S) + H = M(S)`
  have hdiff : t - m ∈ (reach2 S).addStab := by
    refine (hker (t - m)).mp ?_
    rw [map_sub, hmt, sub_self]
  have : t ∈ reach2 S + (reach2 S).addStab := by
    have := Finset.add_mem_add hm hdiff
    simpa using this
  exact target_notMem_reach2_add_addStab hfail this

/-! ### Theorem 4.8(ii): maximality captures the whole kernel -/

/-- **Theorem 4.8(ii)**: a maximal failing support contains every
nonzero class of the stabilizer of its reach. For `w ∈ H` the summand
`A_w ⊆ H` stabilizes `M(S)`, so `M(S ∪ {w}) = M(S)` still fails; `w`
must already be in `S`. -/
theorem addStab_erase_zero_subset_of_maximal (hmax : MaximalFailing S t) :
    (reach2 S).addStab.erase 0 ⊆ S := by
  intro w hw
  rw [Finset.mem_erase] at hw
  by_contra hwS
  have hext := hmax.2 w hw.1 hwS
  rw [reach2_insert hwS] at hext
  have hsub : budget2 w + reach2 S ⊆ reach2 S := by
    calc budget2 w + reach2 S ⊆ (reach2 S).addStab + reach2 S :=
          Finset.add_subset_add_right (budget2_subset_addStab hw.2)
      _ = reach2 S := Finset.addStab_add _
  exact hmax.1 (hsub hext)

/-! ### Theorem 4.8(iii): the container -/

variable [Fintype G]

/-- The container of Theorem 4.8: `(H \ {0}) ∪ φ⁻¹(T̄)`. -/
def container (H : Finset G) (φ : G →+ G') (T : Finset G') : Finset G :=
  (H.erase 0) ∪ Finset.univ.filter (fun x => φ x ∈ T)

/-- **Theorem 4.8(iii)**: every failing support sits inside the
container built from the stabilizer and the projected support. -/
theorem support_subset_container (hS0 : (0 : G) ∉ S) (φ : G →+ G') :
    S ⊆ container (reach2 S).addStab φ
      ((S \ (reach2 S).addStab).image φ) := by
  intro v hv
  rw [container, Finset.mem_union]
  by_cases hvH : v ∈ (reach2 S).addStab
  · left
    rw [Finset.mem_erase]
    exact ⟨by rintro rfl; exact hS0 hv, hvH⟩
  · right
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ ?_⟩
    exact Finset.mem_sdiff.mpr ⟨hv, hvH⟩

/-! ### The size bookkeeping of Theorem 4.8 -/

/-- Every fiber of a hom is at most as large as its kernel (it is a
coset of the kernel, or empty). -/
lemma card_fiber_le (φ : G →+ G') (w : G') :
    #(Finset.univ.filter (fun x : G => φ x = w))
      ≤ #(Finset.univ.filter (fun x : G => φ x = 0)) := by
  classical
  rcases (Finset.univ.filter (fun x : G => φ x = w)).eq_empty_or_nonempty
    with he | ⟨y, hy⟩
  · simp [he]
  · rw [Finset.mem_filter] at hy
    refine Finset.card_le_card_of_injOn (fun x => x - y) ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
        true_and] at hx ⊢
      rw [map_sub, hx, hy.2, sub_self]
    · intro a _ b _ hab
      exact sub_left_inj.mp hab

/-- The preimage of a finset downstairs has at most `#T · #ker` elements. -/
lemma card_preimage_le (φ : G →+ G') (T : Finset G') :
    #(Finset.univ.filter (fun x : G => φ x ∈ T))
      ≤ #T * #(Finset.univ.filter (fun x : G => φ x = 0)) := by
  classical
  have hbi : Finset.univ.filter (fun x : G => φ x ∈ T)
      = T.biUnion (fun w => Finset.univ.filter (fun x : G => φ x = w)) := by
    ext x
    simp [Finset.mem_biUnion, Finset.mem_filter, eq_comm]
  rw [hbi]
  calc #(T.biUnion (fun w => Finset.univ.filter (fun x : G => φ x = w)))
      ≤ ∑ w ∈ T, #(Finset.univ.filter (fun x : G => φ x = w)) :=
        Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ T, #(Finset.univ.filter (fun x : G => φ x = 0)) :=
        Finset.sum_le_sum fun w _ => card_fiber_le φ w
    _ = #T * #(Finset.univ.filter (fun x : G => φ x = 0)) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Theorem 4.8, size bookkeeping**: the container has at most
`(h − 1) + h·#T̄` elements, `h = #H`. -/
lemma card_container_le (H : Finset G) (φ : G →+ G') (T : Finset G')
    (h0 : (0 : G) ∈ H) (hker : ∀ x : G, φ x = 0 ↔ x ∈ H) :
    #(container H φ T) ≤ (#H - 1) + #T * #H := by
  classical
  have hkerf : Finset.univ.filter (fun x : G => φ x = 0) = H := by
    ext x
    simp [Finset.mem_filter, hker x]
  calc #(container H φ T)
      ≤ #(H.erase 0) + #(Finset.univ.filter (fun x : G => φ x ∈ T)) :=
        Finset.card_union_le _ _
    _ ≤ (#H - 1) + #T * #H := by
        rw [Finset.card_erase_of_mem h0, ← hkerf]
        exact Nat.add_le_add_left (card_preimage_le φ T) _

end Reach

/-! ### The quotient `φ_H : ZMod d → ZMod d̄` -/

section Quotient

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The stabilizer of a nonempty finset, as an additive subgroup. -/
def addStabSubgroup {s : Finset G} (hs : s.Nonempty) : AddSubgroup G where
  carrier := ↑s.addStab
  add_mem' := fun ha hb => addStab_add_mem ha hb
  zero_mem' := hs.zero_mem_addStab
  neg_mem' := fun ha => addStab_neg_mem hs ha

/-- Lagrange for the stabilizer: it is a subgroup of order `#s.addStab`,
so `#s.addStab` annihilates each of its elements. -/
lemma nsmul_card_addStab {s : Finset G} (hs : s.Nonempty) {x : G}
    (hx : x ∈ s.addStab) : #s.addStab • x = 0 := by
  classical
  have hcard : Nat.card (addStabSubgroup hs) = #s.addStab :=
    Nat.card_eq_finsetCard s.addStab
  have hx' : x ∈ addStabSubgroup hs := hx
  have h := card_nsmul_eq_zero' (G := addStabSubgroup hs) (x := ⟨x, hx'⟩)
  have h2 := congrArg (Subtype.val) h
  simpa [hcard] using h2

/-- **The quotient of Theorem 4.8**: for a nonempty `M ⊆ ZMod d` with
stabilizer `H` of order `h`, there is `d̄ = d/h` and a hom
`φ_H : ZMod d → ZMod d̄` (reduction mod `d̄`) whose kernel is exactly
`H` — the projection the kernel branch reduces along. -/
theorem exists_addStab_quotient {d : ℕ} [NeZero d] {M : Finset (ZMod d)}
    (hM : M.Nonempty) :
    ∃ (e : ℕ) (φ : ZMod d →+ ZMod e), 0 < e ∧ d = #M.addStab * e ∧
      ∀ x : ZMod d, φ x = 0 ↔ x ∈ M.addStab := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  -- `h = #H` divides `d` (Lagrange, through the stabilizer of `univ`)
  have huniv_stab :
      (Finset.univ : Finset (ZMod d)).addStab = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    rw [Finset.mem_addStab Finset.univ_nonempty]
    exact Finset.vadd_finset_univ
  have hdvd : #M.addStab ∣ d := by
    have hsub : M.addStab ⊆ (Finset.univ : Finset (ZMod d)).addStab := by
      rw [huniv_stab]; exact Finset.subset_univ _
    have h := Finset.card_addStab_dvd_card_addStab hM hsub
    rwa [huniv_stab, Finset.card_univ, ZMod.card] at h
  have hh0 : 0 < #M.addStab := Finset.card_pos.mpr hM.addStab
  obtain ⟨e, he⟩ := hdvd
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · omega
    · exact h
  have hedvd : e ∣ d := ⟨#M.addStab, by rw [Nat.mul_comm]; exact he⟩
  haveI : NeZero e := ⟨by omega⟩
  refine ⟨e, (ZMod.castHom hedvd (ZMod e)).toAddMonoidHom, he0, he, ?_⟩
  -- the kernel, as a finset
  set φ : ZMod d →+ ZMod e :=
    (ZMod.castHom hedvd (ZMod e)).toAddMonoidHom with hφ
  have hval : ∀ x : ZMod d, φ x = 0 ↔ e ∣ x.val := by
    intro x
    have h1 : φ x = ((x.val : ℕ) : ZMod e) := by
      rw [hφ]
      simp [ZMod.castHom_apply, ZMod.natCast_val]
    rw [h1, ZMod.natCast_eq_zero_iff]
  -- `H ⊆ ker φ`, by Lagrange
  have hsub : M.addStab ⊆ Finset.univ.filter (fun x : ZMod d => φ x = 0) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hval x]
    have hlag := nsmul_card_addStab hM hx
    have h2 : ((#M.addStab * x.val : ℕ) : ZMod d) = 0 := by
      push_cast
      rw [← nsmul_eq_mul, ZMod.natCast_zmod_val]
      exact_mod_cast hlag
    rw [ZMod.natCast_eq_zero_iff] at h2
    obtain ⟨c, hc⟩ := h2
    have hkey : #M.addStab * x.val = (#M.addStab * e) * c := by
      rw [← he]; exact hc
    refine ⟨c, Nat.eq_of_mul_eq_mul_left hh0 ?_⟩
    calc #M.addStab * x.val = (#M.addStab * e) * c := hkey
      _ = #M.addStab * (e * c) := by ring
  -- `#ker φ ≤ h`: the kernel sits inside the multiples of `e`
  have hker_le : #(Finset.univ.filter (fun x : ZMod d => φ x = 0))
      ≤ #M.addStab := by
    have hsub2 : Finset.univ.filter (fun x : ZMod d => φ x = 0)
        ⊆ (Finset.range #M.addStab).image
            (fun i => ((i * e : ℕ) : ZMod d)) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨k, hk⟩ := (hval x).mp hx.2
      have hxlt : x.val < d := ZMod.val_lt x
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_range.mpr ?_, ?_⟩
      · nlinarith [hxlt, hk, he, he0, hh0]
      · rw [Nat.mul_comm, ← hk, ZMod.natCast_zmod_val]
    calc #(Finset.univ.filter (fun x : ZMod d => φ x = 0))
        ≤ #((Finset.range #M.addStab).image
            (fun i => ((i * e : ℕ) : ZMod d))) := Finset.card_le_card hsub2
      _ ≤ #(Finset.range #M.addStab) := Finset.card_image_le
      _ = #M.addStab := Finset.card_range _
  have hEq : M.addStab = Finset.univ.filter (fun x : ZMod d => φ x = 0) :=
    Finset.eq_of_subset_of_card_le hsub hker_le
  intro x
  constructor
  · intro h0
    rw [hEq, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h0⟩
  · intro hx
    rw [hEq, Finset.mem_filter] at hx
    exact hx.2

end Quotient

/-! ### One reduction step, with the size bookkeeping -/

section Bookkeeping

open scoped Pointwise

/-- **Theorem 4.8, container size**: one kernel-branch reduction step
for a failing support in `ZMod d`. The support sits in the container
`(H \ {0}) ∪ φ_H⁻¹(T̄)` of Theorem 4.8(iii), whose size is
`(h − 1) + h·#T̄`; Theorem S downstairs (`theoremS_support_bound` at
even `d̄`, `theoremS_support_bound_odd` at odd `d̄`) bounds `#T̄`, and
the bookkeeping closes at `#S ≤ d/2 − 1`. The `d̄ = 2` edge case is
automatic: Theorem S forces `T̄ = ∅` there. -/
theorem kernel_branch_card_bound {d : ℕ} [NeZero d] {S : Finset (ZMod d)}
    {t : ZMod d} (hS0 : (0 : ZMod d) ∉ S) (hfail : Failing S t) :
    #S ≤ d / 2 - 1 := by
  classical
  obtain ⟨e, φ, he0, hde, hker⟩ :=
    exists_addStab_quotient (M := reach2 S) (reach2_nonempty S)
  haveI : NeZero e := ⟨by omega⟩
  set H : Finset (ZMod d) := (reach2 S).addStab with hH
  set T : Finset (ZMod e) := (S \ H).image φ with hT
  -- the projected data
  have hproj : φ t ∉ reach2 T := projected_failing φ hfail hker
  have hT0 : (0 : ZMod e) ∉ T := zero_notMem_projected_support φ hker
  have htne : φ t ≠ 0 := projected_target_ne_zero φ hfail hker
  have hTuniv : ∑ v ∈ T, ({0, v, 2 * v} : Finset (ZMod e)) ≠ Finset.univ := by
    intro hEq
    exact hproj (by rw [reach2_zmod, hEq]; exact Finset.mem_univ _)
  -- `d̄ ≥ 2`: at `d̄ = 1` the projected target could not be nonzero
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · exfalso
      have he1 : e = 1 := by omega
      subst he1
      exact htne (Subsingleton.elim _ _)
    · exact hge
  -- the container bound
  have hH0 : (0 : ZMod d) ∈ H := (reach2_nonempty S).zero_mem_addStab
  have hH1 : 1 ≤ #H := Finset.card_pos.mpr ⟨0, hH0⟩
  have hcard : #S ≤ (#H - 1) + #T * #H :=
    le_trans (Finset.card_le_card (support_subset_container hS0 φ))
      (card_container_le H φ T hH0 hker)
  rcases Nat.even_or_odd e with hEven | hOdd
  · -- even `d̄`: Theorem S gives `#T̄ ≤ d̄/2 − 1`, and the bookkeeping is exact
    have hTle : #T ≤ e / 2 - 1 := theoremS_support_bound hEven hT0 hTuniv
    obtain ⟨f, hf⟩ := hEven
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hTle' : #T ≤ f' := by omega
    have hmul : #T * #H ≤ f' * #H := Nat.mul_le_mul_right _ hTle'
    have hd3 : d = 2 * (f' * #H + #H) :=
      hde.trans (by rw [hf]; ring)
    generalize hX : f' * #H = X at hmul hd3
    generalize #T * #H = A at hcard hmul
    omega
  · -- odd `d̄`: Theorem S gives `#T̄ ≤ (d̄ − 3)/2`, with slack
    have hTle : #T ≤ (e - 3) / 2 := theoremS_support_bound_odd hOdd hT0 hTuniv
    obtain ⟨g, hg⟩ := hOdd
    have he3 : 3 ≤ e := by
      rcases Nat.lt_or_ge e 3 with hlt | hge
      · omega
      · exact hge
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hTle' : #T ≤ g' := by omega
    have hmul : #T * #H ≤ g' * #H := Nat.mul_le_mul_right _ hTle'
    have hd3 : d = 2 * (g' * #H) + 3 * #H :=
      hde.trans (by rw [hg]; ring)
    generalize hX : g' * #H = X at hmul hd3
    generalize #T * #H = A at hcard hmul
    omega


/-- **Theorem 4.8 (kernel branch; lossless reduction), packaged** for
`ZMod d`: a failing support `S` misses the whole `H`-saturation of its
reach; along the quotient `φ_H : ZMod d → ZMod d̄` (`d = h·d̄`) the
projected target `t̄ = φ_H t` is nonzero, the projected support
`T̄ = φ_H(S \ H)` consists of nonzero classes and fails for `t̄` at the
same budget; `S` is contained in the container
`(H \ {0}) ∪ φ_H⁻¹(T̄)`, and that container has at most `d/2 − 1`
elements. (Maximality additionally gives `H \ {0} ⊆ S`:
`addStab_erase_zero_subset_of_maximal`.) -/
theorem kernel_branch {d : ℕ} [NeZero d] {S : Finset (ZMod d)}
    {t : ZMod d} (hS0 : (0 : ZMod d) ∉ S) (hfail : Failing S t) :
    t ∉ reach2 S + (reach2 S).addStab ∧
      ∃ (e : ℕ) (φ : ZMod d →+ ZMod e), 0 < e ∧
        d = #(reach2 S).addStab * e ∧
        (∀ x : ZMod d, φ x = 0 ↔ x ∈ (reach2 S).addStab) ∧
        φ t ≠ 0 ∧
        (0 : ZMod e) ∉ (S \ (reach2 S).addStab).image φ ∧
        Failing ((S \ (reach2 S).addStab).image φ) (φ t) ∧
        S ⊆ container (reach2 S).addStab φ
          ((S \ (reach2 S).addStab).image φ) ∧
        #S ≤ d / 2 - 1 := by
  refine ⟨target_notMem_reach2_add_addStab hfail, ?_⟩
  obtain ⟨e, φ, he0, hde, hker⟩ :=
    exists_addStab_quotient (M := reach2 S) (reach2_nonempty S)
  exact ⟨e, φ, he0, hde, hker, projected_target_ne_zero φ hfail hker,
    zero_notMem_projected_support φ hker, projected_failing φ hfail hker,
    support_subset_container hS0 φ, kernel_branch_card_bound hS0 hfail⟩

end Bookkeeping

/-! ### Proposition 4.12: β-vacuity -/

section BetaVacuity

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Deleting a class splits the reach off one budget-2 summand. -/
lemma reach2_erase_eq {S : Finset G} {v : G} (hv : v ∈ S) :
    reach2 S = budget2 v + reach2 (S.erase v) := by
  conv_lhs => rw [← Finset.insert_erase hv]
  exact reach2_insert (Finset.notMem_erase v S)

/-- Reach membership after a deletion: `M(S) = A ∪ (A + v) ∪ (A + 2v)`
with `A = M(S \ {v})`. -/
lemma mem_reach2_iff_of_mem {S : Finset G} {v : G} (hv : v ∈ S) {z : G} :
    z ∈ reach2 S ↔ z ∈ reach2 (S.erase v) ∨ z - v ∈ reach2 (S.erase v)
      ∨ z - (v + v) ∈ reach2 (S.erase v) := by
  rw [reach2_erase_eq hv, Finset.mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simp only [budget2, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · left; simpa using hb
    · right; left; simpa using hb
    · right; right; simpa using hb
  · rintro (h | h | h)
    · exact ⟨0, by simp [budget2], z, h, by abel⟩
    · exact ⟨v, by simp [budget2], z - v, h, by abel⟩
    · exact ⟨v + v, by simp [budget2], z - (v + v), h, by abel⟩

/-- Deleting a class shrinks the reach. -/
lemma reach2_erase_subset {S : Finset G} {v : G} (hv : v ∈ S) :
    reach2 (S.erase v) ⊆ reach2 S := by
  intro z hz
  exact (mem_reach2_iff_of_mem hv).mpr (Or.inl hz)

/-- Translation of a complement. -/
lemma vadd_compl (a : G) (s : Finset G) : a +ᵥ sᶜ = (a +ᵥ s)ᶜ := by
  ext z
  simp only [Finset.mem_vadd_finset, Finset.mem_compl, vadd_eq_add]
  constructor
  · rintro ⟨w, hw, rfl⟩ ⟨u, hu, hcon⟩
    exact hw (by rwa [show u = w from by linear_combination (norm := abel) hcon] at hu)
  · intro h
    refine ⟨z - a, fun hmem => h ⟨z - a, hmem, by abel⟩, by abel⟩

/-- **Proposition 4.12 (β-vacuity)**: if the deletion step at `v` is
Kneser-critical of *punctured* type — the complement of
`A = M(S \ {v})` is the miss set `F = ZMod d \ M(S)` together with two
isolated punctures `x, y` (isolation: `x − v, y − v ∈ A`) — then
`F − v = F`, so `v` stabilizes the reach. -/
theorem betaVacuity {S : Finset G} {v x y : G} (hv : v ∈ S)
    (hpunct : ∀ z : G, z ∉ reach2 (S.erase v) → z ∉ reach2 S ∨ z = x ∨ z = y)
    (hx : x - v ∈ reach2 (S.erase v)) (hy : y - v ∈ reach2 (S.erase v)) :
    v ∈ (reach2 S).addStab := by
  classical
  set A : Finset G := reach2 (S.erase v) with hA
  -- the miss set is invariant under subtracting `v`
  have hstep : ∀ f : G, f ∉ reach2 S → f - v ∉ reach2 S := by
    intro f hf
    have hsplit := (mem_reach2_iff_of_mem (z := f) hv)
    have hfA : f ∉ A := fun h => hf (hsplit.mpr (Or.inl h))
    have hf1 : f - v ∉ A := fun h => hf (hsplit.mpr (Or.inr (Or.inl h)))
    have hf2 : f - (v + v) ∉ A := fun h => hf (hsplit.mpr (Or.inr (Or.inr h)))
    rcases hpunct (f - v) hf1 with h | h | h
    · exact h
    · exfalso
      apply hf2
      rw [show f - (v + v) = (f - v) - v from by abel, h]
      exact hx
    · exfalso
      apply hf2
      rw [show f - (v + v) = (f - v) - v from by abel, h]
      exact hy
  -- so `(−v) + Fᶜ = F`, hence `(−v) + M = M`, hence `v +ᵥ M = M`
  have hsub : ((-v) +ᵥ (reach2 S)ᶜ) ⊆ (reach2 S)ᶜ := by
    intro z hz
    rw [Finset.mem_vadd_finset] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Finset.mem_compl] at hw ⊢
    have h := hstep w hw
    rwa [show ((-v) +ᵥ w : G) = w - v from by rw [vadd_eq_add]; abel]
  have heq : ((-v) +ᵥ (reach2 S)ᶜ) = (reach2 S)ᶜ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_vadd_finset])
  rw [vadd_compl] at heq
  have hMeq : (-v) +ᵥ reach2 S = reach2 S := by
    have := congrArg (fun (s : Finset G) => sᶜ) heq
    simpa using this
  rw [Finset.mem_addStab (reach2_nonempty S)]
  calc v +ᵥ reach2 S = v +ᵥ ((-v) +ᵥ reach2 S) := by rw [hMeq]
    _ = (v + -v) +ᵥ reach2 S := (add_vadd _ _ _).symm
    _ = reach2 S := by rw [add_neg_cancel, zero_vadd]

/-- The punctured hypothesis in complement form (the paper's
`ℤ/d \ A = F ⊔ {x, y}`) implies the pointwise form used by
`betaVacuity`. -/
lemma punctured_of_compl {S : Finset G} {v x y : G}
    (hcompl : (reach2 (S.erase v))ᶜ = insert x (insert y (reach2 S)ᶜ)) :
    ∀ z : G, z ∉ reach2 (S.erase v) → z ∉ reach2 S ∨ z = x ∨ z = y := by
  intro z hz
  have h : z ∈ (reach2 (S.erase v))ᶜ := Finset.mem_compl.mpr hz
  rw [hcompl] at h
  simp only [Finset.mem_insert, Finset.mem_compl] at h
  tauto

/-- The complement form is exactly Kneser-criticality of the deletion
step: two new elements, `|M(S)| = |M(S \ {v})| + 2`. -/
lemma card_reach2_of_punctured {S : Finset G} {v x y : G} (hv : v ∈ S)
    (hcompl : (reach2 (S.erase v))ᶜ = insert x (insert y (reach2 S)ᶜ))
    (hxy : x ≠ y) (hxM : x ∈ reach2 S) (hyM : y ∈ reach2 S) :
    #(reach2 S) = #(reach2 (S.erase v)) + 2 := by
  classical
  have hy' : y ∉ (reach2 S)ᶜ := by simp [Finset.mem_compl, hyM]
  have hx' : x ∉ insert y (reach2 S)ᶜ := by
    simp [Finset.mem_insert, Finset.mem_compl, hxy, hxM]
  have hcards : #((reach2 (S.erase v))ᶜ) = #((reach2 S)ᶜ) + 2 := by
    rw [hcompl, Finset.card_insert_of_notMem hx',
      Finset.card_insert_of_notMem hy']
  rw [Finset.card_compl, Finset.card_compl] at hcards
  have h1 : #(reach2 (S.erase v)) ≤ Fintype.card G := Finset.card_le_univ _
  have h2 : #(reach2 S) ≤ Fintype.card G := Finset.card_le_univ _
  have h3 : #(reach2 (S.erase v)) ≤ #(reach2 S) :=
    Finset.card_le_card (reach2_erase_subset hv)
  omega

/-- **Proposition 4.12, "in particular"**: at an *aperiodic* failing
support no deletion step is of punctured type — the chaining of
punctured (cofinite) intermediate reaches is vacuous. -/
theorem betaVacuity_aperiodic {S : Finset G} {v x y : G}
    (hS0 : (0 : G) ∉ S) (hv : v ∈ S)
    (haper : (reach2 S).addStab = 0)
    (hpunct : ∀ z : G, z ∉ reach2 (S.erase v) → z ∉ reach2 S ∨ z = x ∨ z = y)
    (hx : x - v ∈ reach2 (S.erase v)) (hy : y - v ∈ reach2 (S.erase v)) :
    False := by
  have hmem := betaVacuity hv hpunct hx hy
  rw [haper] at hmem
  have hv0 : v = 0 := by
    rwa [← Finset.singleton_zero, Finset.mem_singleton] at hmem
  exact hS0 (hv0 ▸ hv)

end BetaVacuity

/-! ### Complete partitions (the mechanism behind Theorem 4.7) -/

section CompletePartition

open scoped Pointwise

/-- Budget-2 subset sums of a *list* of parts (repetitions allowed):
`∑_i {0, aᵢ, 2aᵢ}` in `ℕ`. -/
def sums2 (L : List ℕ) : Finset ℕ :=
  (L.map fun a => ({0, a, 2 * a} : Finset ℕ)).sum

@[simp] lemma sums2_nil : sums2 [] = {0} := rfl

lemma sums2_cons (a : ℕ) (L : List ℕ) :
    sums2 (a :: L) = ({0, a, 2 * a} : Finset ℕ) + sums2 L := by
  simp [sums2]

/-- A **complete partition**, parts listed largest first: each part is
at most one more than the sum of the parts after it (the chain
condition of Theorem 4.7's construction). -/
def IsCompletePartition : List ℕ → Prop
  | [] => True
  | a :: L => a ≤ 1 + L.sum ∧ IsCompletePartition L

/-- The one-step computation: adding a part `a ≤ 1 + M` to a reach
`[0, 2M]` gives exactly `[0, 2(M + a)]`. -/
lemma triple_add_range (a M : ℕ) (h : a ≤ 1 + M) :
    ({0, a, 2 * a} : Finset ℕ) + Finset.range (2 * M + 1)
      = Finset.range (2 * (M + a) + 1) := by
  ext z
  simp only [Finset.mem_add, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_range]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rcases hx with rfl | rfl | rfl <;> omega
  · intro hz
    rcases le_or_gt z (2 * M) with h1 | h1
    · exact ⟨0, by tauto, z, by omega, by omega⟩
    · rcases le_or_gt z (2 * M + a) with h2 | h2
      · exact ⟨a, by tauto, z - a, by omega, by omega⟩
      · exact ⟨2 * a, by tauto, z - 2 * a, by omega, by omega⟩

/-- **The complete-partition lemma** (behind the paper's Theorem 4.7):
the budget-2 subset sums of a complete partition of `N` are exactly the
interval `[0, 2N]`. Induction on the parts, each step being
`triple_add_range`. -/
theorem sums2_of_completePartition :
    ∀ {L : List ℕ}, IsCompletePartition L →
      sums2 L = Finset.range (2 * L.sum + 1)
  | [], _ => by simp [Finset.range_one]
  | a :: L, h => by
      rw [sums2_cons, sums2_of_completePartition h.2, List.sum_cons]
      rw [triple_add_range a L.sum h.1]
      congr 1
      omega

/-- The reach of a complete partition, transported to `ZMod d`: with
distinct parts (mod `d`) the budget-2 reach is the image of `[0, 2N]`. -/
theorem reach2_of_completePartition {d : ℕ} [NeZero d] {L : List ℕ}
    (hcp : IsCompletePartition L)
    (hnd : (L.map (Nat.cast : ℕ → ZMod d)).Nodup) :
    reach2 (L.map (Nat.cast : ℕ → ZMod d)).toFinset
      = (Finset.range (2 * L.sum + 1)).image (Nat.cast : ℕ → ZMod d) := by
  classical
  -- the reach of a `Nodup` list of classes is the list-indexed sum
  have h1 : reach2 (L.map (Nat.cast : ℕ → ZMod d)).toFinset
      = (((L.map (Nat.cast : ℕ → ZMod d)).map budget2)).sum :=
    List.sum_toFinset _ hnd
  -- and that sum is the pushforward of `sums2 L` along `ℕ → ZMod d`
  have h2 : ∀ M : List ℕ,
      (sums2 M).image (Nat.cast : ℕ → ZMod d)
        = (((M.map (Nat.cast : ℕ → ZMod d)).map budget2)).sum := by
    intro M
    induction M with
    | nil => simp [sums2, budget2, Finset.singleton_zero]
    | cons a M ih =>
        rw [sums2_cons, List.map_cons, List.map_cons, List.sum_cons, ← ih,
          show (Nat.cast : ℕ → ZMod d) = ⇑(Nat.castRingHom (ZMod d)) from rfl,
          Finset.image_add]
        congr 1
        simp [budget2, Finset.image_insert, two_mul]
  rw [h1, ← h2, sums2_of_completePartition hcp]

/-- **Theorem 4.7's failure mechanism**: a complete partition of `N`
with `2N < d` misses every class of `ZMod d` above `2N` — for
`2N = d − 2` exactly the singleton miss at `t = −1`. -/
theorem completePartition_failing {d : ℕ} [NeZero d] {L : List ℕ}
    {t : ZMod d} (hcp : IsCompletePartition L)
    (hnd : (L.map (Nat.cast : ℕ → ZMod d)).Nodup)
    (hlt : 2 * L.sum < d) (ht : 2 * L.sum < t.val) :
    Failing (L.map (Nat.cast : ℕ → ZMod d)).toFinset t := by
  classical
  rw [Failing, reach2_of_completePartition hcp hnd]
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨n, hn, hnt⟩ := hmem
  rw [Finset.mem_range] at hn
  have hval : t.val = n := by
    rw [← hnt, ZMod.val_natCast_of_lt (by omega)]
  omega

end CompletePartition

end ErdosStraus

-- Audit. Everything in this file is symbolic: standard axioms only, no
-- `native_decide`.
#print axioms ErdosStraus.target_notMem_reach2_add_addStab
#print axioms ErdosStraus.projected_target_ne_zero
#print axioms ErdosStraus.zero_notMem_projected_support
#print axioms ErdosStraus.projected_failing
#print axioms ErdosStraus.addStab_erase_zero_subset_of_maximal
#print axioms ErdosStraus.support_subset_container
#print axioms ErdosStraus.card_container_le
#print axioms ErdosStraus.exists_addStab_quotient
#print axioms ErdosStraus.kernel_branch_card_bound
#print axioms ErdosStraus.kernel_branch
#print axioms ErdosStraus.betaVacuity
#print axioms ErdosStraus.card_reach2_of_punctured
#print axioms ErdosStraus.betaVacuity_aperiodic
#print axioms ErdosStraus.sums2_of_completePartition
#print axioms ErdosStraus.reach2_of_completePartition
#print axioms ErdosStraus.completePartition_failing

