/-
The reach ⟺ divisor-certificate bridge: the meta-theorem's reduction
itself.

`reach` (Enumerations.lean) is an abstract model: it computes the set
of classes attainable as bounded-exponent subproducts. This file
proves the model faithful to the integers:

* `mem_reach_iff_subprod` — membership in `reach` is existence of a
  subproduct of the underlying (base, budget) list in that class;
* `isSubprod_primes_iff_dvd` — for a list of primes with budget 1
  each, subproducts are exactly the divisors of the product
  (the fundamental theorem of arithmetic, in the form needed);
* `mem_reach_iff_dvd` — membership in `reach` of the prime-factor
  list of `N` is existence of a divisor of `N` in that class;
* `reach_certificate` — the capstone: if the target class `−m`
  (with `m = p·a`, `4a = p + R`) is in `reach` of the factor list of
  `m²`, then explicit positive integers `k ∣ m²`, `b`, `c` exist with
  `R·b = k + m`, `R·c = m²/k + m`, and the Erdős–Straus identity
  `4abc = p(bc + ac + ab)` — i.e. reach membership at the target
  produces a genuine certificate. `certificate_reach` is the
  divisor-to-reach direction (every divisor class is reached), so
  reach membership of a class is equivalent to the existence of a
  divisor of `m²` in that class;
* budget consolidation (`step_step_same`, `reach_merge`,
  `reach_subperm`, `reach_two_eq_doubled`) — the glue between
  configuration shapes;
* `lemmaS_R19_certificate` — the composed corollary: nine prime
  factors of `(p+19)/4` in pairwise-distinct unit classes ≠ 1 mod 19
  yield an explicit Erdős–Straus certificate at `p`.

The bridge and consolidation layers are symbolic (standard axioms
only); the composed corollary inherits the R = 19 enumeration's
single `native_decide` axiom.
-/
import ErdosStraus.Basic
import ErdosStraus.Bridges

namespace ErdosStraus

open Finset

/-- `IsSubprod l k`: `k` is a product `∏ qᵢ^{eᵢ}` over the list `l` of
(base, budget) pairs with `eᵢ ≤ bᵢ`. -/
inductive IsSubprod : List (ℕ × ℕ) → ℕ → Prop
  | nil : IsSubprod [] 1
  | cons {q b : ℕ} {t : List (ℕ × ℕ)} {e k : ℕ} (he : e ≤ b)
      (h : IsSubprod t k) : IsSubprod ((q, b) :: t) (q ^ e * k)

lemma isSubprod_nil_iff {k : ℕ} : IsSubprod [] k ↔ k = 1 := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact .nil

lemma isSubprod_cons_iff {q b : ℕ} {t : List (ℕ × ℕ)} {k : ℕ} :
    IsSubprod ((q, b) :: t) k ↔
      ∃ e k', e ≤ b ∧ IsSubprod t k' ∧ k = q ^ e * k' := by
  constructor
  · intro h
    cases h with
    | cons he h => exact ⟨_, _, he, h, rfl⟩
  · rintro ⟨e, k', he, h, rfl⟩
    exact .cons he h

/-- **Reach computes subproduct classes.** Membership in the `reach`
of a cast (base, budget) list is existence of an integer subproduct in
that class. -/
theorem mem_reach_iff_subprod {R : ℕ} (l : List (ℕ × ℕ)) (c : ZMod R) :
    c ∈ reach (l.map fun qb => ((qb.1 : ZMod R), qb.2)) ↔
      ∃ k : ℕ, IsSubprod l k ∧ (k : ZMod R) = c := by
  suffices key : ∀ (l : List (ℕ × ℕ)) (A : Finset (ZMod R)) (c : ZMod R),
      (c ∈ (l.map fun qb => ((qb.1 : ZMod R), qb.2)).foldl step A ↔
        ∃ a ∈ A, ∃ k : ℕ, IsSubprod l k ∧ a * (k : ZMod R) = c) by
    rw [reach, key]
    constructor
    · rintro ⟨a, ha, k, hk, hak⟩
      rw [mem_singleton] at ha
      exact ⟨k, hk, by rw [← hak, ha, one_mul]⟩
    · rintro ⟨k, hk, hkc⟩
      exact ⟨1, mem_singleton_self 1, k, hk, by rw [one_mul, hkc]⟩
  intro l
  induction l with
  | nil =>
      intro A c
      simp only [List.map_nil, List.foldl_nil]
      constructor
      · intro hc
        exact ⟨c, hc, 1, .nil, by simp⟩
      · rintro ⟨a, ha, k, hk, hak⟩
        rw [isSubprod_nil_iff] at hk
        subst hk
        rw [← hak]
        simpa using ha
  | cons qb t ih =>
      intro A c
      obtain ⟨q, b⟩ := qb
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]
      constructor
      · rintro ⟨a', ha', k', hk', hak'⟩
        rw [mem_step] at ha'
        obtain ⟨a, ha, e, he, rfl⟩ := ha'
        refine ⟨a, ha, q ^ e * k', .cons he hk', ?_⟩
        rw [← hak']
        push_cast
        ring
      · rintro ⟨a, ha, k, hk, hak⟩
        rw [isSubprod_cons_iff] at hk
        obtain ⟨e, k', he, hk', rfl⟩ := hk
        refine ⟨a * (q : ZMod R) ^ e, ?_, k', hk', ?_⟩
        · rw [mem_step]
          exact ⟨a, ha, e, he, rfl⟩
        · rw [← hak]
          push_cast
          ring

/-- **Subproducts of a prime list are its divisors** (the fundamental
theorem of arithmetic, in list form): with budget 1 per occurrence,
the subproducts of a list of primes are exactly the divisors of its
product. -/
theorem isSubprod_primes_iff_dvd :
    ∀ (l : List ℕ), (∀ q ∈ l, q.Prime) → ∀ k : ℕ,
      (IsSubprod (l.map fun q => (q, 1)) k ↔ k ∣ l.prod)
  | [], _, k => by
      simp only [List.map_nil, isSubprod_nil_iff, List.prod_nil,
        Nat.dvd_one]
  | q :: t, hprime, k => by
      have hq : q.Prime := hprime q List.mem_cons_self
      have ht : ∀ r ∈ t, r.Prime := fun r hr =>
        hprime r (List.mem_cons_of_mem q hr)
      simp only [List.map_cons, List.prod_cons]
      constructor
      · rw [isSubprod_cons_iff]
        rintro ⟨e, k', he, hk', rfl⟩
        have hdvd : k' ∣ t.prod :=
          (isSubprod_primes_iff_dvd t ht k').mp hk'
        interval_cases e
        · simpa using hdvd.mul_left q
        · rw [pow_one]
          exact mul_dvd_mul_left q hdvd
      · intro hdvd
        by_cases hqk : q ∣ k
        · obtain ⟨k', rfl⟩ := hqk
          have hk' : k' ∣ t.prod :=
            (Nat.mul_dvd_mul_iff_left hq.pos).mp hdvd
          have := (isSubprod_primes_iff_dvd t ht k').mpr hk'
          rw [isSubprod_cons_iff]
          exact ⟨1, k', le_rfl, this, by rw [pow_one]⟩
        · have hcop : k.Coprime q :=
            ((hq.coprime_iff_not_dvd).mpr hqk).symm
          have hk : k ∣ t.prod := hcop.dvd_of_dvd_mul_left hdvd
          have := (isSubprod_primes_iff_dvd t ht k).mpr hk
          rw [isSubprod_cons_iff]
          exact ⟨0, k, Nat.zero_le 1, this, by rw [pow_zero, one_mul]⟩

/-- The `reach` configuration describing the divisors of `N`: one
(class, budget 1) entry per occurrence of a prime in `N`'s
factorization. -/
def divisorConfig (R : ℕ) (N : ℕ) : List (ZMod R × ℕ) :=
  N.primeFactorsList.map fun (q : ℕ) => ((q : ZMod R), (1 : ℕ))

lemma divisorConfig_eq (R N : ℕ) :
    divisorConfig R N = (N.primeFactorsList.map fun q => (q, 1)).map
      (fun qb => ((qb.1 : ZMod R), qb.2)) := by
  unfold divisorConfig
  rw [List.map_map]
  rfl

/-- **The divisor bridge.** Membership in the `reach` of the
prime-factor configuration of `N` (budget 1 per occurrence) is
existence of a divisor of `N` in that class. -/
theorem mem_reach_iff_dvd {R : ℕ} (N : ℕ) (hN : N ≠ 0) (c : ZMod R) :
    c ∈ reach (divisorConfig R N) ↔
      ∃ k : ℕ, k ∣ N ∧ (k : ZMod R) = c := by
  rw [divisorConfig_eq, mem_reach_iff_subprod]
  constructor
  · rintro ⟨k, hk, hkc⟩
    refine ⟨k, ?_, hkc⟩
    rw [← Nat.prod_primeFactorsList hN]
    exact (isSubprod_primes_iff_dvd _
      (fun q hq => Nat.prime_of_mem_primeFactorsList hq) k).mp hk
  · rintro ⟨k, hk, hkc⟩
    refine ⟨k, ?_, hkc⟩
    apply (isSubprod_primes_iff_dvd _
      (fun q hq => Nat.prime_of_mem_primeFactorsList hq) k).mpr
    rwa [Nat.prod_primeFactorsList hN]

/-- Trivial converse of the capstone: every divisor class is reached. -/
theorem certificate_reach {R : ℕ} (N : ℕ) (hN : N ≠ 0) (k : ℕ)
    (hk : k ∣ N) :
    ((k : ZMod R)) ∈ reach (divisorConfig R N) :=
  (mem_reach_iff_dvd N hN _).mpr ⟨k, hk, rfl⟩

/-- **The meta-theorem's reduction, capstone.** If the target class
`−m` (where `m = p·a` and `4a = p + R`) lies in the `reach` of the
prime-factor list of `m²`, then a genuine residual certificate exists:
a divisor `k ∣ m²` and positive integers `b, c` with `R·b = k + m`,
`R·c = m²/k + m`, satisfying the Erdős–Straus identity
`4abc = p(bc + ca + ab)`. Combined with `certificate_reach`
(divisors ⟶ reach), reach membership of a class is equivalent to the
existence of a divisor of `m²` in that class, and reach membership of
the target produces the explicit certificate — the reduction behind
every finite enumeration in this development. (The remaining step,
that any solution of the equation yields such a divisor, is the
elementary completeness argument of the paper's §1.1 and is not
formalized.) Coprimality of `R` and `m` is
automatic in the application (`p` prime, `p > R`, `gcd(a, R) = 1`
from `4a = p + R`); it is a hypothesis here. -/
theorem reach_certificate (R p a : ℕ) (hR : 0 < R) (hp : 0 < p)
    (ha : 0 < a) (h4 : 4 * a = p + R)
    (hcop : Nat.Coprime R (p * a))
    (hreach : (-(((p * a) : ℕ) : ZMod R)) ∈
      reach (divisorConfig R ((p * a) ^ 2))) :
    ∃ k b c : ℕ, k ∣ (p * a) ^ 2 ∧ R * b = k + p * a ∧
      R * c = (p * a) ^ 2 / k + p * a ∧ 0 < b ∧ 0 < c ∧
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  haveI : NeZero R := ⟨hR.ne'⟩
  set m : ℕ := p * a with hm_def
  have hm0 : m ≠ 0 := by positivity
  obtain ⟨k, hkdvd, hkc⟩ :=
    (mem_reach_iff_dvd (m ^ 2) (pow_ne_zero 2 hm0) _).mp hreach
  have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hkdvd (by positivity)
  obtain ⟨k', hkk'⟩ := hkdvd
  have hk'0 : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h | h
    · rw [h, Nat.mul_zero] at hkk'
      exact absurd hkk' (by positivity)
    · exact h
  -- R ∣ k + m from the class equation
  have hdvd1 : R ∣ k + m := by
    have h0 : ((k + m : ℕ) : ZMod R) = 0 := by
      push_cast
      rw [hkc]
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  -- R ∣ k' + m via the identity m(k'+m) = k'(k+m)
  have hkey : m * (k' + m) = k' * (k + m) := by
    have hmm : m * m = k * k' := by
      rw [← pow_two]
      exact hkk'
    calc m * (k' + m) = m * k' + m * m := by ring
      _ = m * k' + k * k' := by rw [hmm]
      _ = k' * (k + m) := by ring
  have hdvd2 : R ∣ k' + m := by
    have h1 : R ∣ k' * (k + m) := hdvd1.mul_left k'
    rw [← hkey] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨b, hb⟩ := hdvd1
  obtain ⟨c, hc⟩ := hdvd2
  have hquot : m ^ 2 / k = k' := by
    rw [hkk', Nat.mul_div_cancel_left k' hk0]
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, Nat.mul_zero] at hb
      omega
    · exact h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, Nat.mul_zero] at hc
      omega
    · exact h
  refine ⟨k, b, c, ⟨k', hkk'⟩, hb.symm, by rw [hquot]; exact hc.symm,
    hb0, hc0, ?_⟩
  -- the Erdős–Straus identity, via `certificate_sound` over ℤ
  have hZ := certificate_sound (p : ℤ) (R : ℤ) (a : ℤ) (m : ℤ) (k : ℤ)
    (k' : ℤ) (b : ℤ) (c : ℤ)
    (by exact_mod_cast hR.ne')
    (by exact_mod_cast h4)
    (by exact_mod_cast hm_def)
    (by exact_mod_cast hkk'.symm)
    (by exact_mod_cast hb.symm)
    (by exact_mod_cast hc.symm)
  exact_mod_cast hZ

/-! ### Budget consolidation

The glue between configuration shapes: merging equal-class entries,
sub-permutation monotonicity, and the expansion of budget-2 entries
into two budget-1 entries. Together these let the `_mult` enumeration
theorems (budget 2 per distinct class) compose with `divisorConfig`
(budget 1 per prime occurrence). -/

section Consolidation

variable {R : ℕ}

/-- Two steps on the same class merge into one with the summed
budget. -/
lemma step_step_same (A : Finset (ZMod R)) (x : ZMod R) (b₁ b₂ : ℕ) :
    step (step A (x, b₁)) (x, b₂) = step A (x, b₁ + b₂) := by
  ext z
  simp only [mem_step]
  constructor
  · rintro ⟨s, ⟨t, ht, e₁, he₁, rfl⟩, e₂, he₂, rfl⟩
    exact ⟨t, ht, e₁ + e₂, by omega, by rw [pow_add]; ring⟩
  · rintro ⟨t, ht, e, he, rfl⟩
    exact ⟨t * x ^ min e b₁, ⟨t, ht, min e b₁, min_le_right _ _, rfl⟩,
      e - min e b₁, by omega, by rw [mul_assoc, ← pow_add]; congr 2; omega⟩

/-- Merging adjacent equal-class entries preserves `reach`. -/
lemma reach_merge (x : ZMod R) (b₁ b₂ : ℕ) (t : List (ZMod R × ℕ)) :
    reach ((x, b₁) :: (x, b₂) :: t) = reach ((x, b₁ + b₂) :: t) := by
  show List.foldl step _ _ = List.foldl step _ _
  simp only [List.foldl_cons, step_step_same]

/-- `reach` is monotone under sub-permutations. -/
lemma reach_subperm {l L : List (ZMod R × ℕ)} (h : l.Subperm L) :
    reach l ⊆ reach L := by
  obtain ⟨l', hperm, hsub⟩ := h
  rw [← reach_perm hperm]
  exact reach_sublist hsub

/-- A budget-2 configuration equals the doubled budget-1
configuration. -/
lemma reach_two_eq_doubled (ns : List ℕ) :
    reach (ns.map fun (q : ℕ) => ((q : ZMod R), (2 : ℕ))) =
      reach ((ns.flatMap fun q => [q, q]).map
        fun (q : ℕ) => ((q : ZMod R), (1 : ℕ))) := by
  show List.foldl step _ _ = List.foldl step _ _
  generalize ({1} : Finset (ZMod R)) = A
  induction ns generalizing A with
  | nil => rfl
  | cons q t ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append,
        List.foldl_cons, List.singleton_append, List.map_nil,
        List.nil_append, List.foldl_append] at ih ⊢
      rw [show step (step A ((q : ZMod R), 1)) ((q : ZMod R), 1) =
        step A ((q : ZMod R), 2) from step_step_same A _ 1 1]
      exact ih _

end Consolidation

/-! ### The composed corollary: Lemma S in action at R = 19

Everything assembled: if `a = (p+19)/4` has nine prime factors in
distinct unit classes other than 1 modulo 19, the Erdős–Straus
equation is solvable at `p` with first denominator `a` — machine
checked end to end (the finite enumeration by the evaluator, all
bridges symbolic). -/

section Composed

open Finset in
/-- **Lemma S applied (R = 19).** Let `p` be prime with `p > 19`,
`4a = p + 19`, and suppose `qs` lists nine primes dividing `a` whose
classes mod 19 are pairwise distinct and avoid `{0, 1}`. Then an
explicit Erdős–Straus certificate exists at `p`. -/
theorem lemmaS_R19_certificate
    (p a : ℕ) (hp : p.Prime) (hp19 : 19 < p) (ha : 0 < a)
    (h4 : 4 * a = p + 19)
    (qs : List ℕ) (hlen : qs.length = 9)
    (hq_prime : ∀ q ∈ qs, q.Prime)
    (hq_dvd : ∀ q ∈ qs, q ∣ a)
    (hq_cls : ∀ q ∈ qs, ((q : ZMod 19) ≠ 0 ∧ (q : ZMod 19) ≠ 1))
    (hq_nodup : (qs.map fun (q : ℕ) => (q : ZMod 19)).Nodup) :
    ∃ k b c : ℕ, k ∣ (p * a) ^ 2 ∧ 19 * b = k + p * a ∧
      19 * c = (p * a) ^ 2 / k + p * a ∧ 0 < b ∧ 0 < c ∧
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  have h19 : (19 : ℕ).Prime := by norm_num
  -- 19 divides neither p nor a
  have h19p : ¬ (19 ∣ p) := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq h19 hp).mp h
    omega
  have h19a : ¬ (19 ∣ a) := by
    intro h
    exact h19p (by omega : (19 : ℕ) ∣ p)
  have hcop : Nat.Coprime 19 (p * a) := by
    rcases (Nat.Prime.coprime_iff_not_dvd h19).mpr
      (fun h => (h19.dvd_mul.mp h).elim h19p h19a) with h
    exact h
  -- p divides a is impossible (a < p), so p ∉ qs
  have hpa : ¬ (p ∣ a) := by
    intro h
    have := Nat.le_of_dvd ha h
    omega
  have hp_not_mem : p ∉ qs := fun h => hpa (hq_dvd p h)
  -- the support
  have hqs_nodup : qs.Nodup := hq_nodup.of_map
  set T : Finset (ZMod 19) :=
    (qs.map fun (q : ℕ) => (q : ZMod 19)).toFinset with hT_def
  have hT : T ∈ powersetCard 9
      ((univ : Finset (ZMod 19)).filter fun x => x ≠ 0 ∧ x ≠ 1) := by
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rw [hT_def, List.mem_toFinset, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      simp only [mem_filter, mem_univ, true_and]
      exact hq_cls q hq
    · rw [hT_def, List.toFinset_card_of_nodup hq_nodup,
        List.length_map, hlen]
  -- the configuration list
  set l : List (ZMod 19 × ℕ) :=
    qs.map (fun (q : ℕ) => ((q : ZMod 19), (2 : ℕ))) with hl_def
  have hl_nodup : l.Nodup := by
    rw [hl_def, show (fun (q : ℕ) => ((q : ZMod 19), (2 : ℕ))) =
      (fun x : ZMod 19 => (x, (2 : ℕ))) ∘ (fun (q : ℕ) => (q : ZMod 19))
      from rfl, ← List.map_map]
    exact hq_nodup.map (fun x y h => (Prod.ext_iff.mp h).1)
  have hl_mem : ∀ xb : ZMod 19 × ℕ, xb ∈ l ↔ xb.1 ∈ T ∧ xb.2 = 2 := by
    intro xb
    rw [hl_def, List.mem_map, hT_def]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, rfl⟩), rfl⟩
    · rintro ⟨hx1, hx2⟩
      rw [List.mem_toFinset, List.mem_map] at hx1
      obtain ⟨q, hq, hqx⟩ := hx1
      exact ⟨q, hq, by cases xb; simp_all⟩
  -- p's class is a unit
  have hpz : (p : ZMod 19) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact h19p
  -- the enumeration theorem
  have htarget := lemmaS_finite_R19_mult T hT l hl_nodup hl_mem p hpz
  -- consolidate into the divisor configuration of (p·a)²
  set m : ℕ := p * a with hm_def
  have hm0 : m ≠ 0 := by positivity
  have hsub : reach (l ++ [((p : ZMod 19), 2)]) ⊆
      reach (divisorConfig 19 (m ^ 2)) := by
    have hshape : l ++ [((p : ZMod 19), 2)] =
        (qs ++ [p]).map fun (q : ℕ) => ((q : ZMod 19), (2 : ℕ)) := by
      rw [hl_def, List.map_append]
      rfl
    rw [hshape, reach_two_eq_doubled]
    apply reach_subperm
    -- the doubled ℕ-list sub-permutes the prime list of m²
    have hnat : ((qs ++ [p]).flatMap fun q => [q, q]).Subperm
        (m ^ 2).primeFactorsList := by
      rw [List.subperm_ext_iff]
      intro r hr
      have hrmem : r ∈ qs ++ [p] := by
        rw [List.mem_flatMap] at hr
        obtain ⟨q, hq, hrq⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrq
        rcases hrq with rfl | rfl <;> exact hq
      have hr_prime : r.Prime := by
        rcases List.mem_append.mp hrmem with h | h
        · exact hq_prime r h
        · simp only [List.mem_singleton] at h
          subst h; exact hp
      have hr_dvd : r ∣ m := by
        rcases List.mem_append.mp hrmem with h | h
        · exact (hq_dvd r h).mul_left p
        · simp only [List.mem_singleton] at h
          subst h; exact Dvd.intro a rfl
      -- left count = 2
      have hcount2 : ∀ (ns : List ℕ), ns.Nodup → r ∈ ns →
          (ns.flatMap fun q => [q, q]).count r = 2 := by
        intro ns
        induction ns with
        | nil => intro _ h; cases h
        | cons q t ih =>
            intro hnd hmem
            rw [List.flatMap_cons, List.count_append]
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · have hnot : r ∉ (t.flatMap fun q => [q, q]) := by
                intro hcontra
                rw [List.mem_flatMap] at hcontra
                obtain ⟨w, hw, hrw⟩ := hcontra
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                  at hrw
                rcases hrw with rfl | rfl <;>
                  exact (List.nodup_cons.mp hnd).1 hw
              rw [List.count_cons_self, List.count_cons_self,
                List.count_nil, List.count_eq_zero_of_not_mem hnot]
            · have hne : r ≠ q := fun h =>
                (List.nodup_cons.mp hnd).1 (h ▸ hmem')
              rw [List.count_cons_of_ne hne.symm,
                List.count_cons_of_ne hne.symm, List.count_nil]
              simpa using ih (List.nodup_cons.mp hnd).2 hmem'
      have hnodup_full : (qs ++ [p]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hqs_nodup, List.nodup_singleton p, ?_⟩
        intro x hx y hy hxy
        have hyp : y = p := by simpa using hy
        exact hp_not_mem ((hxy.trans hyp) ▸ hx)
      rw [hcount2 (qs ++ [p]) hnodup_full hrmem]
      -- right count = factorization of m², which is ≥ 2
      rw [Nat.primeFactorsList_count_eq, Nat.factorization_pow,
        Finsupp.smul_apply, smul_eq_mul]
      have := hr_prime.factorization_pos_of_dvd hm0 hr_dvd
      omega
    obtain ⟨l', hperm, hsubl⟩ := hnat
    exact ⟨l'.map fun (q : ℕ) => ((q : ZMod 19), (1 : ℕ)),
      hperm.map _, by
        rw [divisorConfig]
        exact hsubl.map _⟩
  -- the target classes agree: −m ≡ −4⁻¹p² (mod 19)
  have h4inv : (4 : ZMod 19)⁻¹ * 4 = 1 := by
    rw [ZMod.inv_eq_of_mul_eq_one 19 4 5 (by decide)]
    decide
  have ha' : (a : ZMod 19) = (4 : ZMod 19)⁻¹ * (p : ZMod 19) := by
    have h4' : (4 : ZMod 19) * (a : ℕ) = ((p : ℕ) : ZMod 19) := by
      have hc : ((4 * a : ℕ) : ZMod 19) = ((p + 19 : ℕ) : ZMod 19) := by
        rw [h4]
      push_cast at hc
      rw [hc, show (19 : ZMod 19) = 0 from by decide, add_zero]
    have := congrArg (fun z => (4 : ZMod 19)⁻¹ * z) h4'
    simpa [← mul_assoc, h4inv] using this
  have htgt_eq : (-(((p * a) : ℕ) : ZMod 19)) =
      -(4⁻¹ : ZMod 19) * (p : ZMod 19) ^ 2 := by
    push_cast
    rw [ha']
    ring
  have hfinal : (-(((p * a) : ℕ) : ZMod 19)) ∈
      reach (divisorConfig 19 ((p * a) ^ 2)) := by
    rw [htgt_eq]
    exact hsub htarget
  -- apply the capstone
  exact reach_certificate 19 p a (by norm_num) hp.pos ha h4 hcop hfinal

end Composed

end ErdosStraus

-- Audit: the divisor bridge and consolidation layers are fully
-- symbolic — standard axioms only; the composed corollary inherits
-- exactly the R = 19 enumeration's single `native_decide` axiom.
#print axioms ErdosStraus.mem_reach_iff_subprod
#print axioms ErdosStraus.isSubprod_primes_iff_dvd
#print axioms ErdosStraus.mem_reach_iff_dvd
#print axioms ErdosStraus.reach_certificate
#print axioms ErdosStraus.certificate_reach
#print axioms ErdosStraus.reach_merge
#print axioms ErdosStraus.reach_subperm
#print axioms ErdosStraus.lemmaS_R19_certificate
