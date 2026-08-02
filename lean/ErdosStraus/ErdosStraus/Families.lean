/-
Proposition 1.9 of the paper (aggregate identity families; "Theorem I"
in the development notes) and the hard-class local facts. The two
family theorems are corollaries of `certificate_sound`; the hard-class
facts are direct finite checks.
-/
import ErdosStraus.Basic

namespace ErdosStraus

/-- **Aggregate identities, first family** (Proposition 1.9). If `R ∣ p + 1` (with the usual residual
setup), then `k = a·p²` certifies: explicit `b, c` exist with the
Erdős–Straus identity. -/
theorem family_p_plus_one
    (p R a m : ℤ) (hR : R ≠ 0)
    (ha : 4 * a = p + R) (hm : m = p * a)
    (hdvd : R ∣ p + 1) :
    ∃ b c : ℤ, R * b = a * p ^ 2 + m ∧ R * c = a + m ∧
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  have hb : R ∣ a * p ^ 2 + m := by
    rw [show a * p ^ 2 + m = a * p * (p + 1) from by rw [hm]; ring]
    exact hdvd.mul_left _
  have hc : R ∣ a + m := by
    rw [show a + m = a * (p + 1) from by rw [hm]; ring]
    exact hdvd.mul_left _
  obtain ⟨b, hb'⟩ := hb
  obtain ⟨c, hc'⟩ := hc
  exact ⟨b, c, hb'.symm, hc'.symm,
    certificate_sound p R a m (a * p ^ 2) a b c hR ha hm
      (by rw [hm]; ring) hb'.symm hc'.symm⟩

/-- **Aggregate identities, second family** (Proposition 1.9). If `R ∣ p + 4` and `R` is odd, then
`k = a²·p` certifies. -/
theorem family_p_plus_four
    (p R a m : ℤ) (hR : R ≠ 0) (hRodd : Odd R)
    (ha : 4 * a = p + R) (hm : m = p * a)
    (hdvd : R ∣ p + 4) :
    ∃ b c : ℤ, R * b = a ^ 2 * p + m ∧ R * c = p + m ∧
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  -- R ∣ 4(a+1); R odd is coprime to 4; hence R ∣ a + 1.
  have h4 : R ∣ 4 * (a + 1) := by
    obtain ⟨t, ht⟩ := hdvd
    exact ⟨t + 1, by linarith⟩
  have hcop2 : IsCoprime (2 : ℤ) R := by
    rw [Int.prime_two.coprime_iff_not_dvd]
    intro h
    have h1 : R % 2 = 1 := Int.odd_iff.mp hRodd
    omega
  have hcop4 : IsCoprime R (4 : ℤ) := by
    rw [show (4 : ℤ) = 2 * 2 from by norm_num]
    exact hcop2.symm.mul_right hcop2.symm
  have ha1 : R ∣ a + 1 := hcop4.dvd_of_dvd_mul_left h4
  have hb : R ∣ a ^ 2 * p + m := by
    rw [show a ^ 2 * p + m = a * p * (a + 1) from by rw [hm]; ring]
    exact ha1.mul_left _
  have hc : R ∣ p + m := by
    rw [show p + m = p * (a + 1) from by rw [hm]; ring]
    exact ha1.mul_left _
  obtain ⟨b, hb'⟩ := hb
  obtain ⟨c, hc'⟩ := hc
  exact ⟨b, c, hb'.symm, hc'.symm,
    certificate_sound p R a m (a ^ 2 * p) p b c hR ha hm
      (by rw [hm]; ring) hb'.symm hc'.symm⟩

/-- The six hard classes are exactly the squares of units mod 840
(witnesses: 1², 11², 13², 17², 19², 23²). -/
theorem hard_classes_are_squares :
    ∀ h ∈ [1, 121, 169, 289, 361, 529],
      ∃ s < 840, Nat.gcd s 840 = 1 ∧ s ^ 2 % 840 = h := by
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by norm_num⟩
  · exact ⟨11, by norm_num⟩
  · exact ⟨13, by norm_num⟩
  · exact ⟨17, by norm_num⟩
  · exact ⟨19, by norm_num⟩
  · exact ⟨23, by norm_num⟩

/-- Corollary J1, arithmetic core: every hard class is ≡ 1 (mod 8),
≡ 1 (mod 3), a QR mod 5, and a QR mod 7. -/
theorem hard_classes_local :
    ∀ h ∈ [1, 121, 169, 289, 361, 529],
      h % 8 = 1 ∧ h % 3 = 1 ∧ (h % 5 = 1 ∨ h % 5 = 4) ∧
        (h % 7 = 1 ∨ h % 7 = 2 ∨ h % 7 = 4) := by decide

end ErdosStraus

-- Audit: standard axioms only.
#print axioms ErdosStraus.family_p_plus_one
#print axioms ErdosStraus.family_p_plus_four
#print axioms ErdosStraus.hard_classes_are_squares
#print axioms ErdosStraus.hard_classes_local
