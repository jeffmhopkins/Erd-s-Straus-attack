/-
The Burgess–reciprocity ladder, elementary layer (Section 5.1 of the
paper; §2.10 of THEORY.md): Lemma J° (composite reciprocity), Lemma N
(Jacobi necessity), and the selected-residual corollary.

All four declarations in this file are fully verified (no `sorry`);
the `#print axioms` audit at the bottom confirms only the standard
axioms are used. See lean/README.md for scope and roadmap.
-/
import ErdosStraus.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace ErdosStraus

open ZMod

/-- **Lemma J° (composite reciprocity, Lemma 5.1 of the paper).** For
any residual `R ≡ 3 (mod 4)` — prime or composite — and any odd prime
`q` with `q ∣ p + R` (so `q` divides the shifted value `(p+R)/4` up to
the unit `4`): `(q | R) = (p | q)`, the left symbol now Jacobi. This is
Theorem J (`reciprocity_structure`) with the primality of `R` dropped;
the paper's coprimality hypothesis `gcd(q, R) = 1` turns out not to be
needed for the identity (when `q ∣ R` both sides vanish). -/
theorem composite_reciprocity
    (p R q : ℕ) [Fact q.Prime]
    (hR4 : R % 4 = 3) (hq2 : q ≠ 2)
    (hdvd : (q : ℤ) ∣ (p : ℤ) + (R : ℤ)) :
    jacobiSym (q : ℤ) R = legendreSym q p := by
  have hq_odd : q % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd (Fact.out : q.Prime)).resolve_left hq2
  have hR_odd : Odd R := Nat.odd_iff.mpr (by omega)
  -- R ≡ −p (mod q), hence (R | q) = χ₄ q · (p | q), exactly as in
  -- `reciprocity_structure`
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
  -- Jacobi reciprocity, with (R−1)/2 odd because R ≡ 3 (mod 4)
  have hrec := jacobiSym.quadratic_reciprocity
    (Nat.odd_iff.mpr hq_odd) hR_odd
  have hRhalf : Odd (R / 2) := Nat.odd_iff.mpr (by omega)
  have hsign : ((-1 : ℤ)) ^ (q / 2 * (R / 2)) = (-1) ^ (q / 2) := by
    rw [mul_comm, pow_mul, hRhalf.neg_one_pow]
  have hchi : (χ₄ q : ℤ) = (-1 : ℤ) ^ (q / 2) :=
    ZMod.χ₄_eq_neg_one_pow hq_odd
  have hchisq : (χ₄ q : ℤ) * χ₄ q = 1 := by
    rw [hchi, ← pow_add, ← two_mul, pow_mul]; norm_num
  have hJleg : jacobiSym (R : ℤ) q = legendreSym q (R : ℤ) :=
    (jacobiSym.legendreSym.to_jacobiSym q (R : ℤ)).symm
  calc jacobiSym (q : ℤ) R
      = (-1 : ℤ) ^ (q / 2 * (R / 2)) * jacobiSym (R : ℤ) q := hrec
    _ = χ₄ q * legendreSym q (R : ℤ) := by rw [hsign, ← hchi, hJleg]
    _ = χ₄ q * (χ₄ q * legendreSym q (p : ℤ)) := by rw [h1]
    _ = legendreSym q (p : ℤ) := by rw [← mul_assoc, hchisq, one_mul]

/-- Multiplicative closure behind Lemma N: if every prime factor of `M`
has Jacobi symbol `+1` mod `R`, then every divisor of `M` does. The
Jacobi analogue of `divisor_one_mod_three`. -/
theorem divisor_jacobiSym_one {R M : ℕ} (hM : M ≠ 0)
    (hfac : ∀ q : ℕ, q.Prime → q ∣ M → jacobiSym (q : ℤ) R = 1) :
    ∀ n : ℕ, n ∣ M → jacobiSym (n : ℤ) R = 1 := by
  intro n
  induction n using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
      intro h0
      exact absurd (Nat.eq_zero_of_zero_dvd h0) hM
  | h₂ u hu =>
      intro _
      rw [Nat.isUnit_iff.mp hu, Nat.cast_one, jacobiSym.one_left]
  | h₃ n q hn hq ih =>
      intro hdvd
      have hqM : q ∣ M := (dvd_mul_right q n).trans hdvd
      have hnM : n ∣ M := (dvd_mul_left n q).trans hdvd
      have h1 := hfac q hq.nat_prime hqM
      have h2 := ih hnM
      rw [Nat.cast_mul, jacobiSym.mul_left, h1, h2, one_mul]

/-- **Lemma N (Jacobi necessity, Lemma 5.2 of the paper).** For a
residual `R ≡ 3 (mod 4)` at a prime `p` with `4a = p + R`: if every
prime factor of `a` has Jacobi symbol `+1` mod `R`, then residual `R`
fails at `p` — no divisor `k` of `m² = (p·a)²` lies in the class
`−m (mod R)`. Consistency gives `(p | R) = (4a | R) = (a | R) = +1`
(`4` is a square), so every divisor of `m²` has symbol `+1`, while the
target class has `(−m | R) = (−1 | R)·(m | R) = −1`. -/
theorem jacobi_necessity
    (p R a : ℕ) (hp : p.Prime) (hR4 : R % 4 = 3) (ha0 : a ≠ 0)
    (ha : 4 * a = p + R)
    (hfac : ∀ q : ℕ, q.Prime → q ∣ a → jacobiSym (q : ℤ) R = 1) :
    ∀ k, k ∣ (p * a) ^ 2 → ¬ (R ∣ k + p * a) := by
  have hR_odd : Odd R := Nat.odd_iff.mpr (by omega)
  have hM0 : (p * a) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.mul_ne_zero hp.ne_zero ha0)
  -- (a | R) = 1 by multiplicative closure
  have haR : jacobiSym (a : ℤ) R = 1 :=
    divisor_jacobiSym_one ha0 hfac a dvd_rfl
  -- consistency: p ≡ 4a (mod R) and (4 | R) = 1, so (p | R) = (a | R)
  have hpR : jacobiSym (p : ℤ) R = 1 := by
    have haZ : (4 : ℤ) * a = p + R := by exact_mod_cast ha
    have hcong : (p : ℤ) ≡ 4 * (a : ℤ) [ZMOD (R : ℤ)] :=
      Int.modEq_iff_dvd.mpr ⟨1, by omega⟩
    calc jacobiSym (p : ℤ) R
        = jacobiSym (4 * (a : ℤ)) R :=
          jacobiSym.mod_left'
            (show (p : ℤ) % R = 4 * (a : ℤ) % R from hcong)
      _ = jacobiSym (4 : ℤ) R * jacobiSym (a : ℤ) R :=
          jacobiSym.mul_left 4 a R
      _ = 1 := by rw [jacobiSym.at_four hR_odd, one_mul, haR]
  -- every prime factor of m² = (p·a)² has symbol +1 …
  have hall : ∀ q : ℕ, q.Prime → q ∣ (p * a) ^ 2 →
      jacobiSym (q : ℤ) R = 1 := by
    intro q hq hdvd
    have hqm : q ∣ p * a := hq.dvd_of_dvd_pow hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hqm with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]; exact hpR
    · exact hfac q hq h
  -- … hence every divisor does
  have hdiv : ∀ n, n ∣ (p * a) ^ 2 → jacobiSym (n : ℤ) R = 1 :=
    divisor_jacobiSym_one hM0 hall
  -- while the target class −m has symbol −1
  have hmR : jacobiSym ((p * a : ℕ) : ℤ) R = 1 :=
    hdiv (p * a) (dvd_pow_self _ (by norm_num))
  have htarget : jacobiSym (-((p * a : ℕ) : ℤ)) R = -1 := by
    rw [jacobiSym.neg _ hR_odd, hmR, mul_one,
      ZMod.χ₄_nat_three_mod_four hR4]
  -- a divisor k ≡ −m (mod R) would carry both symbols
  intro k hk hRk
  have hk1 : jacobiSym (k : ℤ) R = 1 := hdiv k hk
  have hdvdZ : (R : ℤ) ∣ (k : ℤ) + (p * a : ℕ) := by exact_mod_cast hRk
  have hcong : (k : ℤ) ≡ -((p * a : ℕ) : ℤ) [ZMOD (R : ℤ)] :=
    Int.modEq_iff_dvd.mpr
      (by rw [show -((p * a : ℕ) : ℤ) - k = -((k : ℤ) + (p * a : ℕ)) by
                ring]
          exact dvd_neg.mpr hdvdZ)
  have hcontra : jacobiSym (k : ℤ) R = -1 := by
    rw [jacobiSym.mod_left'
      (show (k : ℤ) % R = -((p * a : ℕ) : ℤ) % R from hcong), htarget]
  rw [hk1] at hcontra
  norm_num at hcontra

/-- **Selected-residual corollary (Section 5.1 of the paper).** For a
hard-prime-style configuration — `q` an odd prime at which `p` is a
Legendre non-residue, `(p | q) = −1`, and `R ≡ 3 (mod 4)` a residual
with `4q ∣ p + R` (the selected residual `R₀ = (−p) mod 4q` and every
rung `R₀ + 4qj` of its ladder qualify): `(q | R) = −1`. So the
all-residue failure mode of Lemma N cannot occur at `R` — the prime
`q ∣ (p+R)/4` carries Jacobi symbol `−1` by construction. -/
theorem selected_residual_nonresidue
    (p R q : ℕ) [Fact q.Prime]
    (hR4 : R % 4 = 3) (hq2 : q ≠ 2)
    (hdvd : 4 * q ∣ p + R) (hnr : legendreSym q p = -1) :
    jacobiSym (q : ℤ) R = -1 := by
  have hq : (q : ℤ) ∣ (p : ℤ) + (R : ℤ) := by
    have h : q ∣ p + R := (dvd_mul_left q 4).trans hdvd
    exact_mod_cast h
  rw [composite_reciprocity p R q hR4 hq2 hq, hnr]

end ErdosStraus

-- Audit: these must report only standard axioms (no `sorryAx`, no
-- `native_decide` — this layer is fully symbolic).
#print axioms ErdosStraus.composite_reciprocity
#print axioms ErdosStraus.divisor_jacobiSym_one
#print axioms ErdosStraus.jacobi_necessity
#print axioms ErdosStraus.selected_residual_nonresidue
