/-
Theorem S in the multiplicative divisor-class model.

`TheoremS.lean` proves the support bound symbolically, but in the
*additive* model: for a finite abelian group `G` and a set `S` of
nonzero elements, `M(S) = ∑_{v ∈ S} {0, v, 2v} ≠ G` forces
`#S ≤ max(⌊(g + t − 2)/2⌋, g/2 − 1)`. The paper's Theorem 1.11(ii) is
the *multiplicative* reading of that bound at `G = (ℤ/R)*`: if the
prime factors of `(p+R)/4` occupy at least `(R−1)/2` unit classes
other than `1`, then **every** unit class mod `R` is the class of a
divisor of `m²`, so the certificate condition holds.

This file supplies the missing transfer, for every prime `R` at once:

* `exists_expo_of_mem_reach2` — membership in the budget-2 reach is an
  explicit exponent decomposition with all exponents `≤ 2`;
* `card_two_torsion_filter_le_one` — a unit group of a field carries at
  most one involution, which is what collapses the general bound to
  `g/2 − 1` at `G = (ℤ/R)*`;
* `theoremS_zmod_prod` — the transfer itself: a support of `(R−1)/2`
  unit classes `≠ 1` reaches every nonzero class as a bounded-exponent
  product;
* `theoremS_divisor_class` — the arithmetic form: that product is
  realized by an honest integer divisor of `a²`;
* `theoremS_certificate` — the capstone, composed with
  `reach_certificate` of `DivisorBridge.lean`: explicit positive
  integers `k, b, c` solving the Erdős–Straus equation at `p`.

`lemmaS_R19_certificate` (DivisorBridge.lean) is the same conclusion at
`R = 19`, obtained from the `native_decide` enumeration of
`lemmaS_finite_R19`. `theoremS_certificate` subsumes it for every
prime residual and, unlike it, is symbolic throughout: no
`native_decide`, no per-residual enumeration. Lemma S is thereby a
machine-checked corollary of Theorem S, which the paper asserts
(Remark 5.6) but previously left to the reader.

Everything here is symbolic: standard axioms only.
-/
import ErdosStraus.KernelBranch
import ErdosStraus.DivisorBridge

namespace ErdosStraus

open Finset
open scoped Pointwise

/-! ### An explicit exponent decomposition for the budget-2 reach -/

section Expo

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **Reach membership is an exponent decomposition.** Every element of
`M(S) = ∑_{v ∈ S} {0, v, 2v}` is `∑_{v ∈ S} e_v · v` for an explicit
exponent function bounded by `2`. This is the direction the transfer
needs: the additive theorem certifies that `M(S)` is everything, and
this lemma turns that abstract statement into a concrete product. -/
lemma exists_expo_of_mem_reach2 {S : Finset G} {x : G} (hx : x ∈ reach2 S) :
    ∃ e : G → ℕ, (∀ v, e v ≤ 2) ∧ ∑ v ∈ S, e v • v = x := by
  classical
  induction S using Finset.induction_on generalizing x with
  | empty =>
      refine ⟨fun _ => 0, fun _ => Nat.zero_le 2, ?_⟩
      rw [reach2_empty, Finset.mem_zero] at hx
      simp [hx]
  | insert w S hw ih =>
      rw [reach2_insert hw] at hx
      obtain ⟨b, hb, y, hy, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨e, he, hey⟩ := ih hy
      obtain ⟨j, hj2, hjb⟩ : ∃ j : ℕ, j ≤ 2 ∧ j • w = b := by
        simp only [budget2, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact ⟨0, by omega, by simp⟩
        · exact ⟨1, by omega, by simp⟩
        · exact ⟨2, by omega, by rw [two_smul]⟩
      refine ⟨Function.update e w j, ?_, ?_⟩
      · intro v
        by_cases h : v = w
        · subst h; simpa using hj2
        · simpa [Function.update_of_ne h] using he v
      · have hupd : ∀ v ∈ S, (Function.update e w j) v • v = e v • v := by
          intro v hv
          have hvw : v ≠ w := fun h => hw (h ▸ hv)
          rw [Function.update_of_ne hvw]
        rw [Finset.sum_insert hw, Finset.sum_congr rfl hupd, hey,
          Function.update_self, hjb]

end Expo

/-! ### The unit group of `ZMod R` has at most one involution -/

section Torsion

variable {R : ℕ} [Fact R.Prime]

/-- In a field `x² = 1` has only the roots `±1`, so a set of units
avoiding the identity contains at most one element of order two — the
count `t` of `support_bound_general`, here bounded by `1`. This is what
collapses the general bound `max(⌊(g + t − 2)/2⌋, g/2 − 1)` to
`g/2 − 1` at `G = (ℤ/R)*`, exactly as a single 2-torsion class does in
the cyclic case. -/
lemma card_two_torsion_filter_le_one {S : Finset (Additive (ZMod R)ˣ)}
    (hS0 : (0 : Additive (ZMod R)ˣ) ∉ S) :
    #(S.filter fun v => v + v = 0) ≤ 1 := by
  classical
  have hsub : S.filter (fun v => v + v = 0) ⊆
      {Additive.ofMul (-1 : (ZMod R)ˣ)} := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvS, hv2⟩ := hv
    have hmul : (Additive.toMul v) * (Additive.toMul v) = 1 := hv2
    have hval : ((Additive.toMul v : (ZMod R)ˣ) : ZMod R) *
        ((Additive.toMul v : (ZMod R)ˣ) : ZMod R) = 1 := by
      have := congrArg (fun u : (ZMod R)ˣ => (u : ZMod R)) hmul
      simpa using this
    rcases mul_self_eq_one_iff.mp hval with h | h
    · exfalso
      apply hS0
      have hv1 : Additive.toMul v = 1 := Units.ext h
      have hv0 : v = 0 := by apply Additive.toMul.injective; simpa using hv1
      exact hv0 ▸ hvS
    · rw [Finset.mem_singleton]
      apply Additive.toMul.injective
      exact Units.ext (by simpa using h)
  calc #(S.filter fun v => v + v = 0)
      ≤ #({Additive.ofMul (-1 : (ZMod R)ˣ)} : Finset (Additive (ZMod R)ˣ)) :=
        Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

end Torsion

/-! ### Theorem S, multiplicative form -/

section Multiplicative

variable {R : ℕ} [Fact R.Prime]

/-- **Theorem S in the unit group** (paper Theorem 1.11(ii),
multiplicative form). If `T` is a set of at least `(R−1)/2` units of
`ℤ/R`, none of them the identity, then every unit is a product
`∏_{v ∈ T} v^{e_v}` with all exponents at most `2`.

This is `support_bound_general` transported along
`Additive : (ℤ/R)* ≃ Additive (ℤ/R)*`, with `Fintype.card (ℤ/R)* = R−1`
and the involution count bounded by
`card_two_torsion_filter_le_one`. -/
theorem theoremS_units_prod (hR2 : R ≠ 2)
    (T : Finset (ZMod R)ˣ) (h1 : (1 : (ZMod R)ˣ) ∉ T)
    (hcard : (R - 1) / 2 ≤ #T) (u : (ZMod R)ˣ) :
    ∃ e : (ZMod R)ˣ → ℕ, (∀ v, e v ≤ 2) ∧ ∏ v ∈ T, v ^ e v = u := by
  classical
  have hp : R.Prime := Fact.out
  have hR3 : 3 ≤ R := by have h2 := hp.two_le; omega
  have hodd : Odd R := hp.odd_of_ne_two hR2
  -- the support, moved into the additive copy
  set S : Finset (Additive (ZMod R)ˣ) :=
    T.map (Additive.ofMul (α := (ZMod R)ˣ)).toEmbedding with hS_def
  have hScard : #S = #T := by rw [hS_def, Finset.card_map]
  have hS0 : (0 : Additive (ZMod R)ˣ) ∉ S := by
    rw [hS_def]
    simp only [Finset.mem_map_equiv]
    simpa using h1
  -- card of the ambient group
  have hcardG : Fintype.card (Additive (ZMod R)ˣ) = R - 1 := by
    simpa using ZMod.card_units R
  -- the reach is everything
  have hfull : reach2 S = Finset.univ := by
    by_contra hne
    have hMS : ∑ v ∈ S, ({0, v, v + v} : Finset (Additive (ZMod R)ˣ))
        ≠ Finset.univ := by
      simpa [reach2, budget2] using hne
    have hb := support_bound_general hS0 hMS
    rw [hcardG] at hb
    have ht := card_two_torsion_filter_le_one (R := R) hS0
    have hRe : 2 ∣ R - 1 := by
      obtain ⟨j, hj⟩ := hodd
      exact ⟨j, by omega⟩
    rcases max_choice ((R - 1 + #(S.filter fun v => v + v = 0) - 2) / 2)
      ((R - 1) / 2 - 1) with hmax | hmax <;> rw [hmax] at hb <;> omega
  -- decompose the target
  have humem : Additive.ofMul u ∈ reach2 S := by rw [hfull]; exact Finset.mem_univ _
  obtain ⟨e', he', hsum⟩ := exists_expo_of_mem_reach2 humem
  refine ⟨fun v => e' (Additive.ofMul v), fun v => he' _, ?_⟩
  apply Additive.ofMul.injective
  rw [hS_def, Finset.sum_map] at hsum
  rw [ofMul_prod, ← hsum]
  refine Finset.sum_congr rfl ?_
  intro v _
  simp only [Equiv.coe_toEmbedding]
  exact ofMul_pow _ _

/-- **Theorem S over `ZMod R`.** The same statement with the units
replaced by nonzero classes: a set `C` of at least `(R−1)/2` classes
mod `R`, none of them `0` or `1`, reaches every nonzero class as a
bounded-exponent product. -/
theorem theoremS_zmod_prod (hR2 : R ≠ 2)
    (C : Finset (ZMod R)) (h0 : (0 : ZMod R) ∉ C) (h1 : (1 : ZMod R) ∉ C)
    (hcard : (R - 1) / 2 ≤ #C) {y : ZMod R} (hy : y ≠ 0) :
    ∃ e : ZMod R → ℕ, (∀ x, e x ≤ 2) ∧ ∏ x ∈ C, x ^ e x = y := by
  classical
  -- the units sitting over `C`
  set T : Finset (ZMod R)ˣ :=
    Finset.univ.filter (fun v : (ZMod R)ˣ => (v : ZMod R) ∈ C) with hT_def
  have hval_inj : Function.Injective (fun v : (ZMod R)ˣ => (v : ZMod R)) :=
    fun _ _ h => Units.ext h
  have hTC : T.image (fun v : (ZMod R)ˣ => (v : ZMod R)) = C := by
    ext x
    simp only [Finset.mem_image, hT_def, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · intro hx
      have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
      have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx0
      exact ⟨hu.unit, by rwa [IsUnit.unit_spec], IsUnit.unit_spec hu⟩
  have hTcard : #T = #C := by
    rw [← hTC, Finset.card_image_of_injective _ hval_inj]
  have hT1 : (1 : (ZMod R)ˣ) ∉ T := by
    rw [hT_def, Finset.mem_filter]
    push_neg
    intro _
    simpa using h1
  obtain ⟨u, rfl⟩ : ∃ u : (ZMod R)ˣ, (u : ZMod R) = y :=
    ⟨(isUnit_iff_ne_zero.mpr hy).unit, IsUnit.unit_spec _⟩
  obtain ⟨e', he', hprod⟩ :=
    theoremS_units_prod hR2 T hT1 (by rw [hTcard]; exact hcard) u
  -- transport the exponents down to `ZMod R`
  have hkey : ∀ v : (ZMod R)ˣ,
      (if h : IsUnit ((v : ZMod R)) then e' h.unit else 0) = e' v := by
    intro v
    have hu : IsUnit ((v : ZMod R)) := v.isUnit
    rw [dif_pos hu]
    congr 1
    exact Units.ext (IsUnit.unit_spec hu)
  refine ⟨fun x => if h : IsUnit x then e' h.unit else 0, ?_, ?_⟩
  · intro x
    by_cases h : IsUnit x
    · simp only [dif_pos h]; exact he' _
    · simp only [dif_neg h]; omega
  · calc ∏ x ∈ C, x ^ (if h : IsUnit x then e' h.unit else 0)
        = ∏ v ∈ T, ((v : ZMod R)) ^
            (if h : IsUnit ((v : ZMod R)) then e' h.unit else 0) := by
          rw [← hTC, Finset.prod_image (fun a _ b _ h => hval_inj h)]
      _ = ∏ v ∈ T, ((v : ZMod R)) ^ e' v :=
          Finset.prod_congr rfl fun v _ => by rw [hkey v]
      _ = ((∏ v ∈ T, v ^ e' v : (ZMod R)ˣ) : ZMod R) := by
          rw [Units.coe_prod]
          exact Finset.prod_congr rfl fun v _ => rfl
      _ = (u : ZMod R) := by rw [hprod]

end Multiplicative

/-! ### The arithmetic form: an honest integer divisor -/

section Divisor

/-- A product of bounded powers of distinct primes dividing `a`
divides `a²`. -/
lemma prod_pow_dvd_sq {a : ℕ} (Q : Finset ℕ)
    (hQp : ∀ q ∈ Q, q.Prime) (hQa : ∀ q ∈ Q, q ∣ a)
    (e : ℕ → ℕ) (he : ∀ q, e q ≤ 2) :
    (∏ q ∈ Q, q ^ e q) ∣ a ^ 2 := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | insert q₀ Q hq₀ ih =>
      rw [Finset.prod_insert hq₀]
      have hq₀p : q₀.Prime := hQp q₀ (Finset.mem_insert_self _ _)
      have hq₀a : q₀ ∣ a := hQa q₀ (Finset.mem_insert_self _ _)
      have hrest := ih (fun q hq => hQp q (Finset.mem_insert_of_mem hq))
        (fun q hq => hQa q (Finset.mem_insert_of_mem hq))
      -- `q₀ ^ e q₀ ∣ a ^ 2`
      have hleft : q₀ ^ e q₀ ∣ a ^ 2 :=
        dvd_trans (pow_dvd_pow q₀ (he q₀)) (pow_dvd_pow_of_dvd hq₀a 2)
      -- coprimality with the rest
      have hcop : Nat.Coprime (q₀ ^ e q₀) (∏ q ∈ Q, q ^ e q) := by
        apply Nat.Coprime.pow_left
        apply Nat.Coprime.prod_right
        intro q hq
        apply Nat.Coprime.pow_right
        have hqp : q.Prime := hQp q (Finset.mem_insert_of_mem hq)
        have hne : q₀ ≠ q := fun h => hq₀ (h ▸ hq)
        exact (Nat.coprime_primes hq₀p hqp).mpr hne
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hleft hrest

variable {R : ℕ} [Fact R.Prime]

/-- **Theorem S, arithmetic form** (the paper's Theorem 1.11(ii)). Let
`a` have at least `(R−1)/2` prime factors in pairwise-distinct unit
classes mod `R`, none of them the identity class. Then *every* nonzero
class mod `R` is the class of a divisor of `a²`.

This is the statement Lemma S was introduced to supply at individual
residuals, now proved for every prime residual at once and without any
enumeration. -/
theorem theoremS_divisor_class (hR2 : R ≠ 2) {a : ℕ} (Q : Finset ℕ)
    (hQp : ∀ q ∈ Q, q.Prime) (hQa : ∀ q ∈ Q, q ∣ a)
    (hQ0 : ∀ q ∈ Q, (q : ZMod R) ≠ 0) (hQ1 : ∀ q ∈ Q, (q : ZMod R) ≠ 1)
    (hinj : ∀ q ∈ Q, ∀ q' ∈ Q, (q : ZMod R) = (q' : ZMod R) → q = q')
    (hcard : (R - 1) / 2 ≤ #Q) {y : ZMod R} (hy : y ≠ 0) :
    ∃ k : ℕ, k ∣ a ^ 2 ∧ (k : ZMod R) = y := by
  classical
  set C : Finset (ZMod R) := Q.image (fun q : ℕ => (q : ZMod R)) with hC_def
  have hinj' : Set.InjOn (fun q : ℕ => (q : ZMod R)) ↑Q := by
    intro x hx y' hy' h
    exact hinj x (Finset.mem_coe.mp hx) y' (Finset.mem_coe.mp hy') h
  have hCcard : #C = #Q := by
    rw [hC_def, Finset.card_image_of_injOn hinj']
  have h0 : (0 : ZMod R) ∉ C := by
    rw [hC_def, Finset.mem_image]
    rintro ⟨q, hq, hq0⟩
    exact hQ0 q hq hq0
  have h1 : (1 : ZMod R) ∉ C := by
    rw [hC_def, Finset.mem_image]
    rintro ⟨q, hq, hq1⟩
    exact hQ1 q hq hq1
  obtain ⟨e, he, hprod⟩ :=
    theoremS_zmod_prod hR2 C h0 h1 (by rw [hCcard]; exact hcard) hy
  refine ⟨∏ q ∈ Q, q ^ e ((q : ZMod R)), ?_, ?_⟩
  · exact prod_pow_dvd_sq Q hQp hQa (fun q => e ((q : ZMod R)))
      (fun q => he _)
  · push_cast
    rw [← hprod, hC_def, Finset.prod_image (fun x hx y' hy' h => hinj x hx y' hy' h)]

end Divisor

/-! ### The capstone: an explicit Erdős–Straus certificate -/

section Certificate

variable {R : ℕ} [Fact R.Prime]

/-- **Lemma S as a corollary of Theorem S, for every prime residual.**
Let `p` be prime, `R < p` a prime residual, `4a = p + R`, and suppose
`a` has at least `(R−1)/2` prime factors in pairwise-distinct classes
mod `R`, none of them `0` or `1`. Then an explicit Erdős–Straus
certificate exists at `p`: positive integers `k ∣ (pa)²`, `b`, `c` with
`R·b = k + pa`, `R·c = (pa)²/k + pa`, and `4abc = p(bc + ac + ab)`.

Compare `lemmaS_R19_certificate`, which is this statement at `R = 19`
and inherits a `native_decide` axiom from the enumeration behind it.
This proof is symbolic throughout. -/
theorem theoremS_certificate (hR2 : R ≠ 2) (p a : ℕ)
    (hp : p.Prime) (hpR : R < p) (ha : 0 < a) (h4 : 4 * a = p + R)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) (hQa : ∀ q ∈ Q, q ∣ a)
    (hQ0 : ∀ q ∈ Q, (q : ZMod R) ≠ 0) (hQ1 : ∀ q ∈ Q, (q : ZMod R) ≠ 1)
    (hinj : ∀ q ∈ Q, ∀ q' ∈ Q, (q : ZMod R) = (q' : ZMod R) → q = q')
    (hcard : (R - 1) / 2 ≤ #Q) :
    ∃ k b c : ℕ, k ∣ (p * a) ^ 2 ∧ R * b = k + p * a ∧
      R * c = (p * a) ^ 2 / k + p * a ∧ 0 < b ∧ 0 < c ∧
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  classical
  have hRp : R.Prime := Fact.out
  have hR0 : 0 < R := hRp.pos
  -- `R` divides neither `p` nor `a`
  have hRnp : ¬ (R ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hRp hp).mp h
    omega
  have hRna : ¬ (R ∣ a) := by
    intro h
    apply hRnp
    have h4a : R ∣ 4 * a := h.mul_left 4
    rw [h4] at h4a
    simpa using Nat.dvd_sub h4a (dvd_refl R)
  have hcop : Nat.Coprime R (p * a) :=
    (Nat.Prime.coprime_iff_not_dvd hRp).mpr
      (fun h => (hRp.dvd_mul.mp h).elim hRnp hRna)
  -- the target class is nonzero
  set m : ℕ := p * a with hm_def
  have hm0 : m ≠ 0 := by
    rw [hm_def]; exact Nat.mul_ne_zero hp.pos.ne' ha.ne'
  have hmz : ((m : ℕ) : ZMod R) ≠ 0 := by
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd hRp).mp hcop
      ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hy : -((m : ℕ) : ZMod R) ≠ 0 := by simpa using hmz
  -- Theorem S supplies a divisor of `a²` in the target class
  obtain ⟨k, hk, hkc⟩ :=
    theoremS_divisor_class (a := a) hR2 Q hQp hQa hQ0 hQ1 hinj hcard hy
  have hkm : k ∣ m ^ 2 := by
    refine hk.trans ?_
    rw [hm_def, mul_pow]
    exact dvd_mul_left _ _
  -- and hence a reach membership, hence the certificate
  have hreach : (-((m : ℕ) : ZMod R)) ∈ reach (divisorConfig R (m ^ 2)) := by
    rw [← hkc]
    exact certificate_reach (m ^ 2) (pow_ne_zero 2 hm0) k hkm
  exact reach_certificate R p a hR0 hp.pos ha h4 hcop hreach

end Certificate

end ErdosStraus

-- Audit. Everything in this file is symbolic: standard axioms only,
-- no `native_decide`. In particular `theoremS_certificate` derives at
-- every prime residual — with no enumeration — the conclusion that
-- `lemmaS_R19_certificate` obtains at `R = 19` from a compiled check.
#print axioms ErdosStraus.exists_expo_of_mem_reach2
#print axioms ErdosStraus.card_two_torsion_filter_le_one
#print axioms ErdosStraus.theoremS_units_prod
#print axioms ErdosStraus.theoremS_zmod_prod
#print axioms ErdosStraus.prod_pow_dvd_sq
#print axioms ErdosStraus.theoremS_divisor_class
#print axioms ErdosStraus.theoremS_certificate
