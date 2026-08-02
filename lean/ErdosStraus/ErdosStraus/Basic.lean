/-
Formalization of the residual framework for the Erdős–Straus conjecture.
Companion to "Residual certificates for the Erdős–Straus conjecture".

All three declarations in this file are fully verified (no `sorry`);
the `#print axioms` audit at the bottom confirms only the standard
axioms are used. See lean/README.md for scope and roadmap.
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace ErdosStraus

open ZMod

/-- **Certificate soundness** (Section 1.1 of the paper). If
`4a = p + R`, `m = p·a`, and `k·k' = m²` with `R·b = k + m` and
`R·c = k' + m`, then `(a, b, c)` satisfies the Erdős–Straus identity
`4abc = p(bc + ac + ab)`. Over ℤ; positivity is a separate check. -/
theorem certificate_sound
    (p R a m k k' b c : ℤ) (hR : R ≠ 0)
    (ha : 4 * a = p + R) (hm : m = p * a)
    (hkk' : k * k' = m ^ 2)
    (hb : R * b = k + m) (hc : R * c = k' + m) :
    4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  apply mul_left_cancel₀ hR2
  linear_combination (R * b * (R * c)) * ha + R * (R * b + R * c) * hm +
    R * hkk' + (R * (R * c) - m * R) * hb + (R * (k + m) - m * R) * hc

/-- Integrality companion: if `k·k' = m²`, `R ∣ k + m`, and `R` is
coprime to `k`, then also `R ∣ k' + m`. -/
theorem certificate_integrality
    (R m k k' : ℤ) (hkk' : k * k' = m ^ 2)
    (hk : R ∣ k + m) (hcop : IsCoprime R k) :
    R ∣ k' + m := by
  have h : k * (k' + m) = m * (k + m) := by linear_combination hkk'
  have hdvd : R ∣ k * (k' + m) := h ▸ (hk.mul_left m)
  exact (hcop.dvd_of_dvd_mul_left) hdvd


/-- **Theorem J (reciprocity structure).** For distinct odd primes
`q, R` with `R ≡ 3 (mod 4)` and `q ∣ p + R` (so `q` divides the shifted
value `(p+R)/4` up to the unit `4`): `(q | R) = (p | q)`. -/
theorem reciprocity_structure
    (p R q : ℕ) [Fact R.Prime] [Fact q.Prime]
    (hR4 : R % 4 = 3) (hq2 : q ≠ 2) (hqR : q ≠ R)
    (hdvd : (q : ℤ) ∣ (p : ℤ) + (R : ℤ)) :
    legendreSym R q = legendreSym q p := by
  have hR2 : R ≠ 2 := by intro h; rw [h] at hR4; norm_num at hR4
  have hq_odd : q % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd (Fact.out : q.Prime)).resolve_left hq2
  have hqR_ndvd : ¬ ((q : ℤ) ∣ (R : ℤ)) := by
    rw [Int.natCast_dvd_natCast]
    exact fun h => hqR ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : q.Prime) (Fact.out : R.Prime)).mp h)
  have hRq0 : ((R : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hqR_ndvd
  -- R ≡ −p (mod q), hence (R | q) = χ₄ q · (p | q)
  have hcong : (R : ℤ) ≡ -(p : ℤ) [ZMOD (q : ℤ)] :=
    Int.modEq_iff_dvd.mpr
      (by rw [show -(p : ℤ) - R = -((p : ℤ) + R) by ring]
          exact dvd_neg.mpr hdvd)
  have h1 : legendreSym q (R : ℤ) = χ₄ q * legendreSym q (p : ℤ) := by
    calc legendreSym q (R : ℤ)
        = legendreSym q ((R : ℤ) % q) := legendreSym.mod q _
      _ = legendreSym q ((-(p : ℤ)) % q) := by
            rw [show (R : ℤ) % q = (-(p : ℤ)) % q from hcong]
      _ = legendreSym q (-(p : ℤ)) := (legendreSym.mod q _).symm
      _ = χ₄ q * legendreSym q (p : ℤ) := legendreSym.at_neg hq2 _
  -- reciprocity, with (R−1)/2 odd because R ≡ 3 (mod 4)
  have hrec := legendreSym.quadratic_reciprocity (p := R) (q := q)
    hR2 hq2 (fun h => hqR h.symm)
  have hR2odd : Odd (R / 2) := Nat.odd_iff.mpr (by omega)
  have hsign : ((-1 : ℤ)) ^ (R / 2 * (q / 2)) = (-1) ^ (q / 2) := by
    rw [pow_mul, hR2odd.neg_one_pow]
  have hchi : χ₄ q = (-1 : ℤ) ^ (q / 2) := ZMod.χ₄_eq_neg_one_pow hq_odd
  have hchine : (χ₄ q : ℤ) ≠ 0 := by
    rw [hchi]; exact pow_ne_zero _ (by norm_num)
  -- (p | q) ≠ 0: otherwise (R | q) = 0 forces q ∣ R
  have hX0 : ((p : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    have : legendreSym q (p : ℤ) = 0 := (legendreSym.eq_zero_iff q _).mpr h0
    have : legendreSym q (R : ℤ) = 0 := by rw [h1, this, mul_zero]
    exact hRq0 ((legendreSym.eq_zero_iff q _).mp this)
  have hX2 : legendreSym q (p : ℤ) ^ 2 = 1 := legendreSym.sq_one q hX0
  -- combine: (χ₄q·X)·Y = χ₄q  ⇒  X·Y = 1  ⇒  Y = X
  have hrec' : χ₄ q * (legendreSym q (p : ℤ) * legendreSym R (q : ℤ))
      = χ₄ q * 1 := by
    rw [mul_one, ← mul_assoc, ← h1]
    calc legendreSym q (R : ℤ) * legendreSym R (q : ℤ)
        = (-1 : ℤ) ^ (R / 2 * (q / 2)) := by exact_mod_cast hrec
      _ = (-1 : ℤ) ^ (q / 2) := hsign
      _ = χ₄ q := hchi.symm
  have hXY : legendreSym q (p : ℤ) * legendreSym R (q : ℤ) = 1 :=
    mul_left_cancel₀ hchine hrec'
  calc legendreSym R (q : ℤ)
      = legendreSym q (p : ℤ) ^ 2 * legendreSym R (q : ℤ) := by
        rw [hX2, one_mul]
    _ = legendreSym q (p : ℤ) *
        (legendreSym q (p : ℤ) * legendreSym R (q : ℤ)) := by ring
    _ = legendreSym q (p : ℤ) := by rw [hXY, mul_one]

end ErdosStraus

-- Audit: these must report only standard axioms (no `sorryAx`).
#print axioms ErdosStraus.certificate_sound
#print axioms ErdosStraus.certificate_integrality
#print axioms ErdosStraus.reciprocity_structure
