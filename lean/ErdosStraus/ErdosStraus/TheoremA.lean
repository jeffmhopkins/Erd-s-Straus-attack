/-
Theorem A (the exact criterion at R = 3), both directions.
-/
import ErdosStraus.Basic

namespace ErdosStraus

/-- Multiplicative closure: if every prime factor of `M` is ≡ 1 (mod 3),
then every divisor of `M` is ≡ 1 (mod 3). -/
theorem divisor_one_mod_three {M : ℕ} (hM : M ≠ 0)
    (hfac : ∀ q, q.Prime → q ∣ M → q % 3 = 1) :
    ∀ n, n ∣ M → n % 3 = 1 := by
  intro n
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      intro h0
      exact absurd (Nat.eq_zero_of_zero_dvd h0) hM
  | h₂ u hu =>
      intro _
      rw [Nat.isUnit_iff.mp hu]
  | h₃ n q hn hq ih =>
      intro hdvd
      have hqM : q ∣ M := (dvd_mul_right q n).trans hdvd
      have hnM : n ∣ M := (dvd_mul_left n q).trans hdvd
      have h1 := hfac q hq.nat_prime hqM
      have h2 := ih hnM
      rw [Nat.mul_mod, h1, h2]

/-- **Theorem A, necessity.** If `p ≡ 1 (mod 3)` is prime and every prime
factor of `a` is ≡ 1 (mod 3), then no divisor `k` of `(p·a)²` satisfies
`k ≡ −p·a (mod 3)`: residual 3 fails. -/
theorem theoremA_necessity
    (p a : ℕ) (hp : p.Prime) (hp3 : p % 3 = 1) (ha0 : a ≠ 0)
    (hfac : ∀ q, q.Prime → q ∣ a → q % 3 = 1) :
    ∀ k, k ∣ (p * a) ^ 2 → ¬ (3 ∣ k + p * a) := by
  have hM0 : (p * a) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.mul_ne_zero hp.ne_zero ha0)
  have hall : ∀ q, q.Prime → q ∣ (p * a) ^ 2 → q % 3 = 1 := by
    intro q hq hdvd
    have : q ∣ p * a := hq.dvd_of_dvd_pow hdvd
    rcases (Nat.Prime.dvd_mul hq).mp this with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]; exact hp3
    · exact hfac q hq h
  intro k hk
  have hk3 : k % 3 = 1 := divisor_one_mod_three hM0 hall k hk
  have hm3 : (p * a) % 3 = 1 % 3 := by
    have ha3 : a % 3 = 1 := divisor_one_mod_three hM0 hall a
      (dvd_pow (dvd_mul_left a p) (by norm_num))
    rw [Nat.mul_mod, hp3, ha3]
  omega

/-- **Theorem A, sufficiency.** If `4a = p + 3`, `p ≡ 1 (mod 3)`, and `a`
has a (positive) divisor `q ≡ 2 (mod 3)`, then residual 3 succeeds with
`k = q`: positive `b, c` exist satisfying the Erdős–Straus identity. -/
theorem theoremA_sufficiency
    (p a q d : ℤ) (hp0 : 0 < p) (ha0 : 0 < a) (hq0 : 0 < q)
    (ha : 4 * a = p + 3) (hp3 : p % 3 = 1) (hq3 : q % 3 = 2)
    (had : a = q * d) :
    ∃ b c : ℤ, 0 < b ∧ 0 < c ∧
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  set m : ℤ := p * a with hm
  set k' : ℤ := p ^ 2 * q * d ^ 2 with hk'
  have hkk' : q * k' = m ^ 2 := by rw [hk', hm, had]; ring
  -- 3 ∣ q + m, purely linearly: 3 ∣ a−1 and 3 ∣ q+p, and
  -- q + pa = (q+p) + p·(a−1).
  have h3 : (3 : ℤ) ∣ q + m := by
    have h1 : (3 : ℤ) ∣ a - 1 := by omega
    have h2 : (3 : ℤ) ∣ q + p := by omega
    obtain ⟨s, hs⟩ := h1
    have hsplit : q + m = (q + p) + 3 * (p * s) := by
      rw [hm]; linear_combination p * hs
    rw [hsplit]
    exact dvd_add h2 ⟨p * s, rfl⟩
  -- coprimality and the codivisor congruence
  have hcop : IsCoprime (3 : ℤ) q := by
    rw [Int.prime_three.coprime_iff_not_dvd]
    intro hdq
    omega
  have h3' : (3 : ℤ) ∣ k' + m :=
    certificate_integrality 3 m q k' hkk' h3 hcop
  obtain ⟨b, hb⟩ := h3
  obtain ⟨c, hc⟩ := h3'
  have hbpos : 0 < b := by
    have hm0 : 0 < m := mul_pos hp0 ha0
    nlinarith
  have hk'pos : 0 < k' := by
    have hm2 : 0 < m ^ 2 := by positivity
    nlinarith
  have hcpos : 0 < c := by
    have hm0 : 0 < m := mul_pos hp0 ha0
    nlinarith
  exact ⟨b, c, hbpos, hcpos,
    certificate_sound p 3 a m q k' b c (by norm_num) ha hm hkk'
      hb.symm hc.symm⟩

end ErdosStraus

-- Audit: standard axioms only.
#print axioms ErdosStraus.theoremA_necessity
#print axioms ErdosStraus.theoremA_sufficiency
