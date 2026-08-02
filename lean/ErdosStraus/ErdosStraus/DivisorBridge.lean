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
  produces a genuine certificate. The converse direction is
  `certificate_reach`.

Everything here is symbolic: standard axioms only.
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
`4abc = p(bc + ca + ab)`. Combined with `certificate_reach`,
solvability of residual `R` at `p` is *equivalent* to reach
membership of the target — the reduction behind every finite
enumeration in this development. Coprimality of `R` and `m` is
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

end ErdosStraus

-- Audit: the divisor bridge is fully symbolic — standard axioms only,
-- no `native_decide` anywhere in this file.
#print axioms ErdosStraus.mem_reach_iff_subprod
#print axioms ErdosStraus.isSubprod_primes_iff_dvd
#print axioms ErdosStraus.mem_reach_iff_dvd
#print axioms ErdosStraus.reach_certificate
