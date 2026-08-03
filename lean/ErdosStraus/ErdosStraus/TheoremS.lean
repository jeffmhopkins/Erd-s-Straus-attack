/-
Theorem S (the paper's Theorem 1.10(i)): the unconditional support
bound, by Kneser's addition theorem.

Statement. Let `d` be even and `S` a set of nonzero elements of
`ZMod d`. If the bounded subset-sum set
`M(S) = ∑_{v ∈ S} {0, v, 2v}` is not all of `ZMod d`, then
`|S| ≤ d/2 − 1`.

The theorem is proved here in its **general form** (the paper's
Theorem 1.10(iii)): in *any* finite abelian group `G` of order `g`,
with `t` the number of involutions occurring in `S`, a failing support
satisfies `|S| ≤ max(⌊(g+t−2)/2⌋, g/2 − 1)`
(`support_bound_general`); the cyclic even case (`|S| ≤ d/2 − 1`,
one involution) and the odd case (`|S| ≤ (d−3)/2`, no involutions) are
both instances. `forbidden_classes_general` is the sieve reading: a
failure forbids at least `(g − t)/2 − 1` non-identity classes.

This is the group-theoretic engine behind Lemma S for *every* residual
`R` at once (in discrete-log or product coordinates, divisor classes
of `m²` realize exactly such an `M(S)`, with `d = |(ℤ/R)ˣ|` even): the
finite checks at `R = 19, 23, 31` (`Enumerations.lean`,
`LemmaS31.lean`) verify special cases of this theorem.

Proof structure (the paper's, exactly):
* Kneser's addition theorem, for two summands, is vendored from Yaël
  Dillies' misc-yd repository (`ErdosStraus/Kneser/`, Apache 2.0, see
  the attribution headers there): with `H = (s + t).addStab`,
  `#(s + H) + #(t + H) ≤ #(s + t) + #H`.
* `add_kneser_list` iterates it to any finite family: with
  `H = (∑ Aᵢ).addStab`, `∑ #(Aᵢ + H) ≤ #(∑ Aᵢ) + (k − 1)·#H`. The
  induction replaces the head summand `B` by `B + H`; the key fact is
  that this does not change the stabilizer (`(t + H).addStab = H`,
  since stabilizers of summands embed in stabilizers of sums).
* `theoremS_support_bound` then splits on `H = M(S).addStab`:
  - `H` trivial: every `{0, v, 2v}` has 3 elements except at most one
    (the 2-torsion class `v = d/2`), so `#M ≥ 3k − 1 − (k − 1) = 2k`,
    and `M ≠ univ` forces `2k ≤ d − 1`, i.e. `k ≤ d/2 − 1` (`d` even).
  - `H` nontrivial of order `h`: `M` misses a whole `H`-coset, so
    `#M ≤ d − h`; classes inside `H` contribute cosets of size `h`
    (at most `h − 1` of them, `0 ∉ S`), classes outside at least `2h`,
    and Kneser gives `k₁ ≤ d/h − 2`, so
    `k ≤ (h − 1) + (d/h − 2) = h + d/h − 3 ≤ d/2 − 1` — the quadratic
    `h² − (d/2 + 2)h + d ≤ 0` for divisors `2 ≤ h ≤ d/2`, and `h = d`
    is impossible (`M` would be everything).

Everything here is symbolic: standard axioms only, no `native_decide`.
-/
import ErdosStraus.Kneser.Kneser
import Mathlib.Tactic

namespace ErdosStraus

open Finset
open scoped Pointwise

/-! ### Iterated Kneser -/

section IteratedKneser

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The pointwise sum of a list of nonempty finsets is nonempty. -/
lemma sum_list_nonempty :
    ∀ (L : List (Finset G)), (∀ A ∈ L, A.Nonempty) → L.sum.Nonempty
  | [], _ => by
      rw [List.sum_nil]
      exact ⟨0, Finset.mem_zero.mpr rfl⟩
  | A :: L, h => by
      rw [List.sum_cons]
      exact (h A (by simp)).add
        (sum_list_nonempty L fun B hB => h B (by simp [hB]))

/-- Auxiliary induction (on a length bound) for `add_kneser_list`. -/
private lemma add_kneser_list_aux :
    ∀ (n : ℕ) (L : List (Finset G)), L.length ≤ n → L ≠ [] →
      (∀ A ∈ L, A.Nonempty) →
      (L.map fun A => #(A + L.sum.addStab)).sum + #L.sum.addStab ≤
        #L.sum + L.length * #L.sum.addStab := by
  intro n
  induction n with
  | zero =>
      intro L hlen hne _
      cases L with
      | nil => exact absurd rfl hne
      | cons A T => simp only [List.length_cons] at hlen; omega
  | succ n ih =>
      intro L hlen hne hA
      cases L with
      | nil => exact absurd rfl hne
      | cons A L' =>
        cases L' with
        | nil =>
            -- singleton list: equality (`A + A.addStab = A`)
            simp only [List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, List.length_cons, List.length_nil, add_zero]
            rw [Finset.add_addStab]
            omega
        | cons B T =>
            have hAne : A.Nonempty := hA A (by simp)
            have hBne : B.Nonempty := hA B (by simp)
            have hDne : (B :: T).sum.Nonempty :=
              sum_list_nonempty _ (fun C hC => hA C (by simp [hC]))
            rw [List.sum_cons] at hDne
            -- normalize the goal to the head split `A + (B + T.sum)`
            simp only [List.map_cons, List.sum_cons, List.length_cons]
            set D := B + T.sum with hD
            set H := (A + D).addStab with hH
            have hMne : (A + D).Nonempty := hAne.add hDne
            have hHne : H.Nonempty := hMne.addStab
            -- two-summand Kneser at the head split
            have hkneser := Finset.add_kneser A D
            rw [← hH] at hkneser
            -- the stabilizer of `D + H` is `H` itself
            have haux : (D + H).addStab = H := by
              apply Finset.Subset.antisymm
              · have h1 : (D + H).addStab ⊆ (A + (D + H)).addStab :=
                  Finset.subset_addStab_add_right hAne
                rwa [← add_assoc, hH, Finset.add_addStab, ← hH] at h1
              · have h3 : H.addStab ⊆ (D + H).addStab :=
                  Finset.subset_addStab_add_right hDne
                rwa [hH, Finset.addStab_idem, ← hH] at h3
            -- induction hypothesis on the head-modified list `(B + H) :: T`
            have hih := ih ((B + H) :: T)
              (by simp only [List.length_cons] at hlen ⊢; omega)
              (by simp)
              (by
                intro C hC
                rcases List.mem_cons.mp hC with rfl | hC
                · exact hBne.add hHne
                · exact hA C (by simp [hC]))
            simp only [List.map_cons, List.sum_cons, List.length_cons] at hih
            have hsum'' : (B + H) + T.sum = D + H := by
              rw [hD]; exact add_right_comm _ _ _
            rw [hsum'', haux] at hih
            -- absorb the extra `H` on the modified head
            have hhead : (B + H) + H = B + H := by
              rw [add_assoc, hH, Finset.addStab_add_addStab]
            rw [hhead] at hih
            -- linear arithmetic
            have e1 : (T.length + 1) * #H = T.length * #H + #H := by ring
            have e2 : (T.length + 1 + 1) * #H = T.length * #H + #H + #H := by
              ring
            rw [e1] at hih
            rw [e2]
            generalize T.length * #H = q at hih ⊢
            omega

/-- **Iterated Kneser theorem** (standard corollary of the two-summand
form): for a nonempty list of nonempty finsets in an abelian group,
with `H` the stabilizer of the total sum,
`∑ᵢ #(Aᵢ + H) ≤ #(∑ᵢ Aᵢ) + (k − 1)·#H` — stated additively (with the
`#H` moved to the left) to avoid truncated subtraction. -/
theorem add_kneser_list (L : List (Finset G)) (hne : L ≠ [])
    (hA : ∀ A ∈ L, A.Nonempty) :
    (L.map fun A => #(A + L.sum.addStab)).sum + #L.sum.addStab ≤
      #L.sum + L.length * #L.sum.addStab :=
  add_kneser_list_aux L.length L le_rfl hne hA

end IteratedKneser

/-! ### Theorem S in a general finite abelian group -/

section General

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- The **involutions** of a finite abelian group: its elements of
order exactly two. In `ZMod d` there is at most one (`d/2`, and only
when `d` is even); in `(ℤ/R)*` there are `2^{ω(R)} − 1`, the count
appearing in the paper's Theorem 1.10(iii). -/
def involutions (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] :
    Finset G :=
  Finset.univ.filter fun v => v + v = 0 ∧ v ≠ 0

/-- **Theorem S in general form** (the paper's Theorem 1.10(iii)). Let
`G` be a *finite abelian group* — no cyclicity, no parity assumption —
and `S` a set of nonzero elements with bounded subset-sum set
`M(S) = ∑_{v ∈ S} {0, v, 2v} ≠ G`. Then
`#S ≤ max(⌊(g + t − 2)/2⌋, g/2 − 1)`, where `g = |G|` and `t` counts
the involutions *occurring in `S`* (so a fortiori the involutions of
`G`).

The proof is the paper's, with the involution count replacing the
single 2-torsion class of the cyclic case: Kneser's addition theorem
in its iterated form (`add_kneser_list`), split on
`H = Stab(M(S))`.
* `H` trivial: `#{0, v, 2v} = 3` except at the involutions of `S`,
  where it is `2`; so `#M ≥ 3k − t − (k − 1) = 2k − t + 1` and
  `M ≠ G` forces `2k ≤ g + t − 2`.
* `H` nontrivial of order `h`: verbatim the cyclic argument —
  `M` misses a whole `H`-coset, the `≤ h − 1` classes of `S` inside
  `H` contribute one coset each and those outside at least two, so
  Kneser gives `k ≤ (h − 1) + (g/h − 2) = h + g/h − 3 ≤ g/2 − 1`, the
  quadratic being `(h − 2)(g/h − 2) ≥ 0`.

`theoremS_support_bound` and `theoremS_support_bound_odd` below are
the two `ZMod d` instances. -/
theorem support_bound_general {S : Finset G} (hS0 : (0 : G) ∉ S)
    (hMS : ∑ v ∈ S, ({0, v, v + v} : Finset G) ≠ Finset.univ) :
    #S ≤ max ((Fintype.card G + #(S.filter fun v => v + v = 0) - 2) / 2)
      (Fintype.card G / 2 - 1) := by
  classical
  haveI : Nonempty G := ⟨0⟩
  have hd0 : 0 < Fintype.card G := Fintype.card_pos
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · simp
  set A : G → Finset G := fun v => {0, v, v + v} with hAdef
  set M : Finset G := ∑ v ∈ S, A v with hMdef
  -- `M` is nonempty (every summand contains `0`)
  have hLne : S.toList.map A ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
    exact hSne.ne_empty
  have hLA : ∀ B ∈ S.toList.map A, B.Nonempty := by
    intro B hB
    rw [List.mem_map] at hB
    obtain ⟨v, _, rfl⟩ := hB
    exact ⟨0, by simp [hAdef]⟩
  have hsumL : (S.toList.map A).sum = M := Finset.sum_map_toList S A
  have hMne : M.Nonempty := by
    rw [← hsumL]
    exact sum_list_nonempty _ hLA
  have h0H : (0 : G) ∈ M.addStab := hMne.zero_mem_addStab
  -- `#M < g`
  have hMlt : #M < Fintype.card G := by
    have h1 : M ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hMS
    have h2 := Finset.card_lt_card h1
    rwa [Finset.card_univ] at h2
  -- stabilizer closure facts
  have hHneg : ∀ {z : G}, z ∈ M.addStab → -z ∈ M.addStab := by
    intro z hz
    rw [Finset.mem_addStab hMne]
    have hz' := (Finset.mem_addStab hMne).mp hz
    calc (-z) +ᵥ M = (-z) +ᵥ (z +ᵥ M) := by rw [hz']
      _ = ((-z) + z) +ᵥ M := (add_vadd _ _ _).symm
      _ = M := by rw [neg_add_cancel, zero_vadd]
  have hHadd : ∀ {y z : G}, y ∈ M.addStab → z ∈ M.addStab →
      y + z ∈ M.addStab := by
    intro y z hy hz
    rw [← Finset.addStab_add_addStab M]
    exact Finset.add_mem_add hy hz
  -- iterated Kneser, instantiated at the family `A`
  have hkneser_sum : ∑ v ∈ S, #(A v + M.addStab) + #M.addStab
      ≤ #M + #S * #M.addStab := by
    have h := add_kneser_list (S.toList.map A) hLne hLA
    rw [hsumL, List.map_map] at h
    have h1 : (S.toList.map ((fun B => #(B + M.addStab)) ∘ A)).sum
        = ∑ v ∈ S, #(A v + M.addStab) := Finset.sum_map_toList S _
    have h2 : (S.toList.map A).length = #S := by
      rw [List.length_map, Finset.length_toList]
    rw [h1, h2] at h
    exact h
  by_cases hHtriv : M.addStab = 0
  · -- trivial stabilizer: `#(A v) ≥ 3` away from the involutions of `S`
    refine le_trans ?_ (le_max_left _ _)
    have hcard0 : #(0 : Finset G) = 1 := rfl
    have hkn : ∑ v ∈ S, #(A v) + 1 ≤ #M + #S := by
      have h := hkneser_sum
      rw [hHtriv] at h
      simp only [add_zero] at h
      rw [hcard0, mul_one] at h
      exact h
    -- cardinalities of the summands
    have hA2 : ∀ v ∈ S, 2 ≤ #(A v) := by
      intro v hv
      have hv0 : v ≠ 0 := by rintro rfl; exact hS0 hv
      have hsub : ({0, v} : Finset G) ⊆ A v := by
        simp only [hAdef]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      have h2 : #({0, v} : Finset G) = 2 := by
        rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact fun h => hv0 h.symm), Finset.card_singleton]
      calc 2 = #({0, v} : Finset G) := h2.symm
        _ ≤ #(A v) := Finset.card_le_card hsub
    have hA3 : ∀ v ∈ S, ¬ v + v = 0 → 3 ≤ #(A v) := by
      intro v hv h2v
      have hv0 : v ≠ 0 := by rintro rfl; exact hS0 hv
      have hne1 : v ∉ ({v + v} : Finset G) := by
        simp only [Finset.mem_singleton]
        intro h
        apply hv0
        have h' : v + 0 = v + v := by rw [add_zero]; exact h
        exact (add_left_cancel h').symm
      have hne0 : (0 : G) ∉ ({v, v + v} : Finset G) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact hv0 h.symm
        · exact h2v h.symm
      simp only [hAdef]
      rw [Finset.card_insert_of_notMem hne0,
        Finset.card_insert_of_notMem hne1, Finset.card_singleton]
    -- assemble
    have hsum_split := Finset.sum_filter_add_sum_filter_not S
      (fun v => v + v = 0) (fun v => #(A v))
    have hcard_split : #(S.filter fun v => v + v = 0)
        + #(S.filter fun v => ¬ v + v = 0) = #S :=
      Finset.card_filter_add_card_filter_not (fun v => v + v = 0)
    have hbb1 : 2 * #(S.filter fun v => v + v = 0)
        ≤ ∑ v ∈ S.filter (fun v => v + v = 0), #(A v) := by
      have h := Finset.card_nsmul_le_sum (S.filter fun v => v + v = 0)
        (fun v => #(A v)) 2 (fun v hv => hA2 v (Finset.mem_of_mem_filter v hv))
      rwa [smul_eq_mul, mul_comm] at h
    have hbb2 : 3 * #(S.filter fun v => ¬ v + v = 0)
        ≤ ∑ v ∈ S.filter (fun v => ¬ v + v = 0), #(A v) := by
      have h := Finset.card_nsmul_le_sum (S.filter fun v => ¬ v + v = 0)
        (fun v => #(A v)) 3 (fun v hv => by
          rw [Finset.mem_filter] at hv
          exact hA3 v hv.1 hv.2)
      rwa [smul_eq_mul, mul_comm] at h
    omega
  · -- nontrivial stabilizer of order `h`: `2 ≤ h`, `h ∣ g`
    refine le_trans ?_ (le_max_right _ _)
    have hH2 : 2 ≤ #M.addStab := by
      have h1 : 0 < #M.addStab := Finset.card_pos.mpr hMne.addStab
      have h2 : #M.addStab ≠ 1 :=
        fun h => hHtriv (Finset.card_addStab_eq_zero.mp h)
      omega
    have huniv_stab : (Finset.univ : Finset G).addStab = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro a
      rw [Finset.mem_addStab Finset.univ_nonempty]
      exact Finset.vadd_finset_univ
    have hdvd : #M.addStab ∣ Fintype.card G := by
      have hsub : M.addStab ⊆ (Finset.univ : Finset G).addStab := by
        rw [huniv_stab]; exact Finset.subset_univ _
      have h := Finset.card_addStab_dvd_card_addStab hMne hsub
      rwa [huniv_stab, Finset.card_univ] at h
    obtain ⟨m, hm⟩ := hdvd
    -- `m ≥ 2`: `m = 0` contradicts `g > 0`, `m = 1` would make `M` everything
    have hm2 : 2 ≤ m := by
      rcases Nat.lt_or_ge m 2 with hlt | hge
      · exfalso
        interval_cases m
        · omega
        · -- `H = univ` forces `M = univ`
          have hHuniv : M.addStab = Finset.univ :=
            Finset.eq_univ_of_card _ (by omega)
          apply hMS
          apply Finset.eq_univ_iff_forall.mpr
          intro x
          obtain ⟨y, hy⟩ := id hMne
          have hx : x - y ∈ M.addStab := hHuniv ▸ Finset.mem_univ _
          have hxM := (Finset.mem_addStab hMne).mp hx
          rw [← hxM]
          have hmem : (x - y) +ᵥ y ∈ (x - y) +ᵥ M :=
            Finset.vadd_mem_vadd_finset hy
          rwa [show (x - y) +ᵥ y = x from by rw [vadd_eq_add]; abel] at hmem
      · exact hge
    -- `M` misses a full coset of the stabilizer
    have hMH : #M + #M.addStab ≤ Fintype.card G := by
      obtain ⟨x, hx⟩ : ∃ x, x ∉ M := by
        by_contra hcon
        push Not at hcon
        exact hMS (Finset.eq_univ_iff_forall.mpr hcon)
      have hdisj : Disjoint M (x +ᵥ M.addStab) := by
        rw [Finset.disjoint_right]
        intro y hy hyM
        rw [Finset.mem_vadd_finset] at hy
        obtain ⟨s, hs, rfl⟩ := hy
        apply hx
        have h1 : (-s) +ᵥ (x +ᵥ s : G) = x := by
          rw [vadd_eq_add, vadd_eq_add]; abel
        have h2 : (-s) +ᵥ M = M := (Finset.mem_addStab hMne).mp (hHneg hs)
        rw [← h1, ← h2]
        exact Finset.vadd_mem_vadd_finset hyM
      have hcard := Finset.card_union_of_disjoint hdisj
      have hle : #(M ∪ (x +ᵥ M.addStab)) ≤ Fintype.card G :=
        Finset.card_le_univ (M ∪ (x +ᵥ M.addStab))
      rw [hcard, Finset.card_vadd_finset] at hle
      exact hle
    -- classes inside the stabilizer contribute exactly one coset …
    have hin : ∀ v ∈ S.filter (fun v => v ∈ M.addStab),
        #(A v + M.addStab) = #M.addStab := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have hvH : v ∈ M.addStab := hv.2
      have h2v : v + v ∈ M.addStab := hHadd hvH hvH
      have hsub : A v ⊆ M.addStab := by
        simp only [hAdef]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h0H
        · exact hvH
        · exact h2v
      have h1 : A v + M.addStab ⊆ M.addStab := by
        calc A v + M.addStab ⊆ M.addStab + M.addStab :=
              Finset.add_subset_add hsub (Finset.Subset.refl _)
          _ = M.addStab := Finset.addStab_add_addStab M
      have h2 : M.addStab ⊆ A v + M.addStab := by
        intro x hx
        have h0 : (0 : G) ∈ A v := by simp [hAdef]
        have h3 := Finset.add_mem_add h0 hx
        rwa [zero_add] at h3
      rw [Finset.Subset.antisymm h1 h2]
    -- … and classes outside at least two
    have hout : ∀ v ∈ S.filter (fun v => v ∉ M.addStab),
        2 * #M.addStab ≤ #(A v + M.addStab) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have hvH : v ∉ M.addStab := hv.2
      have hsub : ({0, v} : Finset G) ⊆ A v := by
        simp only [hAdef]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      have hsub2 : ({0, v} : Finset G) + M.addStab ⊆ A v + M.addStab :=
        Finset.add_subset_add hsub (Finset.Subset.refl _)
      have hcalc : ({0, v} : Finset G) + M.addStab
          = M.addStab ∪ (v +ᵥ M.addStab) := by
        rw [Finset.insert_eq, Finset.union_add, Finset.singleton_add,
          Finset.singleton_add, zero_vadd]
      have hdisj : Disjoint M.addStab (v +ᵥ M.addStab) := by
        rw [Finset.disjoint_right]
        intro z hz hzH
        rw [Finset.mem_vadd_finset] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        apply hvH
        have h2 : (v +ᵥ w) + -w = v := by rw [vadd_eq_add]; abel
        have h3 := hHadd hzH (hHneg hw)
        rwa [h2] at h3
      have hcard2 : #(({0, v} : Finset G) + M.addStab)
          = 2 * #M.addStab := by
        rw [hcalc, Finset.card_union_of_disjoint hdisj,
          Finset.card_vadd_finset]
        ring
      calc 2 * #M.addStab
          = #(({0, v} : Finset G) + M.addStab) := hcard2.symm
        _ ≤ #(A v + M.addStab) := Finset.card_le_card hsub2
    -- the two counting splits
    have hsplitsum := Finset.sum_filter_add_sum_filter_not S
      (fun v => v ∈ M.addStab) (fun v => #(A v + M.addStab))
    have hsplitcard : #(S.filter fun v => v ∈ M.addStab)
        + #(S.filter fun v => ¬ v ∈ M.addStab) = #S :=
      Finset.card_filter_add_card_filter_not (fun v => v ∈ M.addStab)
    have hb1 : ∑ v ∈ S.filter (fun v => v ∈ M.addStab), #(A v + M.addStab)
        = #(S.filter fun v => v ∈ M.addStab) * #M.addStab := by
      rw [Finset.sum_congr rfl hin, Finset.sum_const, smul_eq_mul]
    have hb2 : #(S.filter fun v => ¬ v ∈ M.addStab) * (2 * #M.addStab)
        ≤ ∑ v ∈ S.filter (fun v => ¬ v ∈ M.addStab), #(A v + M.addStab) := by
      have h := Finset.card_nsmul_le_sum
        (S.filter fun v => ¬ v ∈ M.addStab)
        (fun v => #(A v + M.addStab)) (2 * #M.addStab) hout
      rwa [smul_eq_mul] at h
    -- at most `h − 1` classes inside the stabilizer (`0 ∉ S`)
    have hk0 : #(S.filter fun v => v ∈ M.addStab) + 1 ≤ #M.addStab := by
      have hsub : S.filter (fun v => v ∈ M.addStab) ⊆ M.addStab.erase 0 := by
        intro v hv
        rw [Finset.mem_filter] at hv
        rw [Finset.mem_erase]
        exact ⟨by rintro rfl; exact hS0 hv.1, hv.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem h0H] at h1
      omega
    -- the Kneser chain: `k₁·h + 2h ≤ g`
    have hchain : #(S.filter fun v => ¬ v ∈ M.addStab) * #M.addStab
        + 2 * #M.addStab ≤ Fintype.card G := by
      have h1 := hkneser_sum
      rw [← hsplitsum, hb1] at h1
      have h2 : #S * #M.addStab
          = #(S.filter fun v => v ∈ M.addStab) * #M.addStab
            + #(S.filter fun v => ¬ v ∈ M.addStab) * #M.addStab := by
        rw [← add_mul, hsplitcard]
      rw [h2] at h1
      have e3 : #(S.filter fun v => ¬ v ∈ M.addStab) * (2 * #M.addStab)
          = 2 * (#(S.filter fun v => ¬ v ∈ M.addStab) * #M.addStab) := by
        ring
      rw [e3] at hb2
      generalize #(S.filter fun v => v ∈ M.addStab) * #M.addStab = a at h1
      generalize #(S.filter fun v => ¬ v ∈ M.addStab) * #M.addStab = b
        at h1 hb2 ⊢
      omega
    -- divide by `h`: `k₁ ≤ m − 2`
    have hstep2 : #M.addStab * (#(S.filter fun v => ¬ v ∈ M.addStab) + 2)
        ≤ #M.addStab * m := by
      calc #M.addStab * (#(S.filter fun v => ¬ v ∈ M.addStab) + 2)
          = #(S.filter fun v => ¬ v ∈ M.addStab) * #M.addStab
            + 2 * #M.addStab := by ring
        _ ≤ Fintype.card G := hchain
        _ = #M.addStab * m := hm
    have hk1 : #(S.filter fun v => ¬ v ∈ M.addStab) + 2 ≤ m :=
      Nat.le_of_mul_le_mul_left hstep2 (by omega)
    -- the quadratic endgame: `k ≤ h + m − 3 ≤ g/2 − 1`
    obtain ⟨h2, hh2⟩ : ∃ h2, #M.addStab = h2 + 2 := ⟨#M.addStab - 2, by omega⟩
    obtain ⟨m2, hm2'⟩ : ∃ m2, m = m2 + 2 := ⟨m - 2, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q, h2 * m2 = q := ⟨_, rfl⟩
    have hd_expand : Fintype.card G = q + 2 * h2 + 2 * m2 + 4 := by
      rw [hm, hh2, hm2', ← hq]; ring
    omega

/-- **Theorem 1.10(iii), the sieve reading.** A failing support forbids
at least `(g − t)/2 − 1` non-identity classes, where `t = #involutions`
— for `G = (ℤ/R)*`, where `t = 2^{ω(R)} − 1`, this is the paper's
`φ(R)/2 − 2^{ω(R)−1} − 1`, hence sieve dimension
`≥ 1/2 − (2^{ω(R)−1} + 1)/φ(R)`. -/
theorem forbidden_classes_general {S : Finset G} (hS0 : (0 : G) ∉ S)
    (hMS : ∑ v ∈ S, ({0, v, v + v} : Finset G) ≠ Finset.univ) :
    (Fintype.card G - #(involutions G)) / 2 - 1
      ≤ #((Finset.univ.erase (0 : G)) \ S) := by
  classical
  have hsub : S ⊆ Finset.univ.erase (0 : G) := by
    intro v hv
    rw [Finset.mem_erase]
    exact ⟨by rintro rfl; exact hS0 hv, Finset.mem_univ v⟩
  have hcard : #((Finset.univ.erase (0 : G)) \ S)
      = Fintype.card G - 1 - #S := by
    rw [Finset.card_sdiff_of_subset hsub,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hTt : #(S.filter fun v => v + v = 0) ≤ #(involutions G) := by
    apply Finset.card_le_card
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [involutions, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, hv.2, by rintro rfl; exact hS0 hv.1⟩
  have htg : #(involutions G) ≤ Fintype.card G :=
    Finset.card_le_univ (involutions G)
  have hb := support_bound_general hS0 hMS
  rcases max_choice
      ((Fintype.card G + #(S.filter fun v => v + v = 0) - 2) / 2)
      (Fintype.card G / 2 - 1) with hmax | hmax <;>
    rw [hmax] at hb <;> omega

/-- The same bound quoted through any upper estimate `t` for the
involution count — the form in which the paper applies it at
`G = (ℤ/R)*` with `t = 2^{ω(R)} − 1`. -/
theorem forbidden_classes_general_of_le {S : Finset G} (hS0 : (0 : G) ∉ S)
    (hMS : ∑ v ∈ S, ({0, v, v + v} : Finset G) ≠ Finset.univ)
    {t : ℕ} (ht : #(involutions G) ≤ t) :
    (Fintype.card G - t) / 2 - 1 ≤ #((Finset.univ.erase (0 : G)) \ S) :=
  le_trans (by omega) (forbidden_classes_general hS0 hMS)

end General

/-! ### Theorem S over `ZMod d` -/

/-- The two shapes of the budget-2 summand agree over `ZMod d`. -/
private lemma sum_two_mul_eq {d : ℕ} (S : Finset (ZMod d)) :
    ∑ v ∈ S, ({0, v, v + v} : Finset (ZMod d))
      = ∑ v ∈ S, ({0, v, 2 * v} : Finset (ZMod d)) :=
  Finset.sum_congr rfl fun v _ => by rw [two_mul]

/-- **Theorem S** (paper Theorem 1.10(i)): for even `d` and a set `S`
of nonzero elements of `ZMod d`, if the bounded subset-sum set
`M(S) = ∑_{v ∈ S} {0, v, 2v}` is not all of `ZMod d` then
`#S ≤ d/2 − 1`. In the meta-theorem's model, `M(S)` is (the log of)
the divisor-class set of `m²` at minimal multiplicities, so failure of
a residual forces the factor-class support below half the group order
— Lemma S for every residual at once.

Now an instance of `support_bound_general`: a cyclic group of even
order has exactly one involution, so the general bound
`max(⌊(d + t − 2)/2⌋, d/2 − 1)` collapses to `d/2 − 1`. -/
theorem theoremS_support_bound {d : ℕ} [NeZero d] (hd : Even d)
    {S : Finset (ZMod d)} (hS0 : (0 : ZMod d) ∉ S)
    (hMS : ∑ v ∈ S, ({0, v, 2 * v} : Finset (ZMod d)) ≠ Finset.univ) :
    #S ≤ d / 2 - 1 := by
  classical
  obtain ⟨nn, hnn⟩ := hd
  have hMS' : ∑ v ∈ S, ({0, v, v + v} : Finset (ZMod d)) ≠ Finset.univ := by
    rw [sum_two_mul_eq]; exact hMS
  -- at most one nonzero 2-torsion class (`v = d/2`)
  have hT : #(S.filter fun v => v + v = 0) ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    apply ZMod.val_injective d
    have htors : ∀ v ∈ S, v + v = 0 → 2 * v.val = d := by
      intro v hv h2
      have hneg : -v = v := by rw [neg_eq_iff_add_eq_zero]; exact h2
      rcases (ZMod.neg_eq_self_iff v).mp hneg with h0 | hval
      · exact absurd (h0 ▸ hv) hS0
      · exact hval
    have h1 := htors a ha.1 ha.2
    have h2 := htors b hb.1 hb.2
    omega
  have hcard : Fintype.card (ZMod d) = d := ZMod.card d
  have hb := support_bound_general hS0 hMS'
  rw [hcard] at hb
  rcases max_choice ((d + #(S.filter fun v => v + v = 0) - 2) / 2) (d / 2 - 1)
    with hmax | hmax <;> rw [hmax] at hb <;> omega

/-- **Theorem S, odd-modulus variant** (the paper's Theorem 4.8,
parenthetical): for odd `d` and a set `S` of nonzero elements of
`ZMod d`, if `M(S) = ∑_{v ∈ S} {0, v, 2v} ≠ ZMod d` then
`#S ≤ (d − 3)/2`. Needed for the quotients arising in the kernel
branch (`KernelBranch.lean`).

Also an instance of `support_bound_general`: a group of odd order has
*no* involutions, so the general bound reads
`max(⌊(d − 2)/2⌋, d/2 − 1) = (d − 3)/2`. -/
theorem theoremS_support_bound_odd {d : ℕ} [NeZero d] (hd : Odd d)
    {S : Finset (ZMod d)} (hS0 : (0 : ZMod d) ∉ S)
    (hMS : ∑ v ∈ S, ({0, v, 2 * v} : Finset (ZMod d)) ≠ Finset.univ) :
    #S ≤ (d - 3) / 2 := by
  classical
  obtain ⟨nn, hnn⟩ := hd
  have hMS' : ∑ v ∈ S, ({0, v, v + v} : Finset (ZMod d)) ≠ Finset.univ := by
    rw [sum_two_mul_eq]; exact hMS
  -- no 2-torsion at all
  have hT : #(S.filter fun v => v + v = 0) = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv h2
    have hneg : -v = v := by rw [neg_eq_iff_add_eq_zero]; exact h2
    rcases (ZMod.neg_eq_self_iff v).mp hneg with h0 | hval
    · exact hS0 (h0 ▸ hv)
    · omega
  have hcard : Fintype.card (ZMod d) = d := ZMod.card d
  have hb := support_bound_general hS0 hMS'
  rw [hcard] at hb
  rcases max_choice ((d + #(S.filter fun v => v + v = 0) - 2) / 2) (d / 2 - 1)
    with hmax | hmax <;> rw [hmax] at hb <;> omega

end ErdosStraus

-- Audit. Everything in this file (and in the vendored Kneser
-- development it builds on) is symbolic: standard axioms only, no
-- `native_decide`.
#print axioms Finset.add_kneser
#print axioms ErdosStraus.add_kneser_list
#print axioms ErdosStraus.support_bound_general
#print axioms ErdosStraus.forbidden_classes_general
#print axioms ErdosStraus.forbidden_classes_general_of_le
#print axioms ErdosStraus.theoremS_support_bound
#print axioms ErdosStraus.theoremS_support_bound_odd
