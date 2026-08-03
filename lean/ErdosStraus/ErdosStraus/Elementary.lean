/-
The elementary layer of the paper, completed: Proposition 1.1
(completeness), Proposition 2.1 (character obstruction) and
Proposition 2.2 (guaranteed-success classes).

* **Proposition 1.1** says the residual formulation loses nothing: an
  ordered solution `a ≤ b ≤ c` of `4/p = 1/a + 1/b + 1/c` has
  `p/4 < a ≤ 3p/4`, so `R = 4a − p` is an admissible residual in
  `(0, 2p]` and the solution *is* a residual certificate at `R`
  (`completeness`). Conversely a certificate at any admissible `R`
  gives a solution — that direction is `certificate_sound` /
  `certificate_integrality` from `Basic.lean`, reused here. The
  headline is the equivalence `hasAdmissibleCertificate_iff`:
  `R_min(p) ≤ 2p` **iff** the conjecture holds at `p`.
* **Proposition 2.1** is the Legendre special case of `Ladder.lean`'s
  Lemma N: for a prime `r ∣ R` with `r ≡ 3 (mod 4)`, if every prime
  factor of `m = pa` is a quadratic residue mod `r` then no divisor of
  `m²` lies in the class `−m (mod R)`. The multiplicative-closure
  engine is `divisor_jacobiSym_one`, reused rather than reproved.
* **Proposition 2.2** produces certificates: with
  `t ≡ −4⁻¹p² ≡ −m (mod R)`, a prime factor `q` of `a` with
  `q ≡ t·p^{−i} (mod R)`, `i ∈ {0,1,2}` — equivalently
  `q·p^i ≡ −m (mod R)` — makes `k = q·p^i` a certificate, composed
  here with `certificate_sound` into explicit positive `b, c`. The
  "in particular" clause is the fixed class `−4⁻¹`
  (`success_class_minus_quarter`), which certifies regardless of `p`.

All declarations here are fully verified (no `sorry`); the
`#print axioms` audit at the bottom confirms only the standard axioms
are used. See lean/README.md for scope and roadmap.
-/
import ErdosStraus.Basic
import ErdosStraus.Ladder

namespace ErdosStraus

open ZMod

/-! ### Proposition 1.1: completeness -/

/-- The Erdős–Straus equation `4/p = 1/a + 1/b + 1/c` and its cleared
form `4abc = p(bc + ac + ab)` agree for nonzero denominators. -/
theorem erdosStraus_rat_iff {p a b c : ℚ} (hp : p ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    4 / p = 1 / a + 1 / b + 1 / c ↔
      4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  rw [div_add_div _ _ ha hb, div_add_div _ _ (mul_ne_zero ha hb) hc,
    div_eq_div_iff hp (mul_ne_zero (mul_ne_zero ha hb) hc)]
  constructor <;> intro h <;> linear_combination h

/-- **Proposition 1.1, the interval.** For a solution ordered
`a ≤ b ≤ c`, the equation forces `1/a < 4/p ≤ 3/a`, i.e.
`p/4 < a ≤ 3p/4`. -/
theorem ordered_denominator_bounds {p a b c : ℤ} (hp : 0 < p) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (heq : 4 * (a * b * c) = p * (b * c + a * c + a * b)) :
    p < 4 * a ∧ 4 * a ≤ 3 * p := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hac : a * c ≤ b * c := mul_le_mul_of_nonneg_right hab hc.le
  have hab' : a * b ≤ c * b := mul_le_mul_of_nonneg_right (hab.trans hbc) hb.le
  refine ⟨?_, ?_⟩
  · nlinarith [mul_pos hb hc, mul_pos (mul_pos hp ha) hc,
      mul_pos (mul_pos hp ha) hb]
  · nlinarith [mul_pos hb hc, hac, hab']

/-- The admissibility congruence: at a hard prime `p ≡ 1 (mod 4)`, the
residual `R = 4a − p` of any solution is automatically
`≡ 3 (mod 4)`. -/
theorem residual_three_mod_four {p : ℤ} (a : ℤ) (hp : p % 4 = 1) :
    (4 * a - p) % 4 = 3 := by omega

/-- **Proposition 1.1 (completeness).** Every solution of
`4abc = p(bc + ac + ab)` at a prime `p > 0`, ordered `a ≤ b ≤ c`,
satisfies `p/4 < a ≤ 3p/4`; hence `R = 4a − p` is admissible,
`0 < R ≤ 2p`, and the solution **is** a residual certificate at `R`:
there are positive `k, k'` with `k·k' = m²` (`m = pa`, so `k ∣ m²`)
and `R·b = k + m`, `R·c = k' + m` — i.e. `k ≡ −m (mod R)` and `b, c`
are exactly the recovery formulae. -/
theorem completeness {p a b c : ℤ} (hp : 0 < p) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (heq : 4 * (a * b * c) = p * (b * c + a * c + a * b)) :
    p < 4 * a ∧ 4 * a ≤ 3 * p ∧ 0 < 4 * a - p ∧ 4 * a - p ≤ 2 * p ∧
      ∃ k k' : ℤ, 0 < k ∧ 0 < k' ∧ k * k' = (p * a) ^ 2 ∧
        (4 * a - p) * b = k + p * a ∧ (4 * a - p) * c = k' + p * a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  obtain ⟨h1, h2⟩ := ordered_denominator_bounds hp ha hab hbc heq
  -- the single algebraic consequence of the identity: `R·bc = m(b+c)`
  have key : (4 * a - p) * (b * c) = p * a * (b + c) := by linear_combination heq
  refine ⟨h1, h2, by linarith, by linarith, (4 * a - p) * b - p * a,
    (4 * a - p) * c - p * a, ?_, ?_, ?_, by ring, by ring⟩
  · -- `c·k = pab > 0`
    have hck : c * ((4 * a - p) * b - p * a) = p * a * b := by
      linear_combination key
    nlinarith [mul_pos (mul_pos hp ha) hb]
  · -- `b·k' = pac > 0`
    have hbk : b * ((4 * a - p) * c - p * a) = p * a * c := by
      linear_combination key
    nlinarith [mul_pos (mul_pos hp ha) hc]
  · linear_combination (4 * a - p) * key

/-- The conjecture at `p`: a solution of `4/p = 1/a + 1/b + 1/c` in
positive integers (cleared form). -/
def HasESSolution (p : ℤ) : Prop :=
  ∃ a b c : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    4 * (a * b * c) = p * (b * c + a * c + a * b)

/-- `R_min(p) ≤ 2p`: a residual certificate at some admissible residual
`R ∈ (0, 2p]` — a factorization `k·k' = m²` of `m² = (pa)²` with
`4a = p + R` and both `k, k'` in the class `−m (mod R)`. -/
def HasAdmissibleCertificate (p : ℤ) : Prop :=
  ∃ R a k k' : ℤ, 0 < R ∧ R ≤ 2 * p ∧ 4 * a = p + R ∧ 0 < k ∧
    k * k' = (p * a) ^ 2 ∧ R ∣ k + p * a ∧ R ∣ k' + p * a

/-- Auxiliary: an *ordered* solution yields an admissible certificate.
This is `completeness`, repackaged. -/
private theorem hasAdmissibleCertificate_of_ordered {p a b c : ℤ}
    (hp : 0 < p) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (heq : 4 * (a * b * c) = p * (b * c + a * c + a * b)) :
    HasAdmissibleCertificate p := by
  obtain ⟨_, _, hR0, hR2, k, k', hk, _, hkk', hbk, hck⟩ :=
    completeness hp ha hab hbc heq
  exact ⟨4 * a - p, a, k, k', hR0, hR2, by ring, hk, hkk',
    ⟨b, hbk.symm⟩, ⟨c, hck.symm⟩⟩

/-- **Proposition 1.1, headline corollary**: `R_min(p) ≤ 2p` **iff**
the Erdős–Straus conjecture holds at `p`. The `←` direction is
completeness (every solution, sorted, is a certificate at its own
residual `R = 4a − p ≤ 2p`); the `→` direction is
`certificate_sound` together with the positivity of the recovery
formulae. So the conjecture *is* the assertion that the least
admissible residual is at most `2p`. -/
theorem hasAdmissibleCertificate_iff {p : ℤ} (hp : 0 < p) :
    HasAdmissibleCertificate p ↔ HasESSolution p := by
  constructor
  · rintro ⟨R, a, k, k', hR, _, ha4, hk, hkk', ⟨b, hb⟩, ⟨c, hc⟩⟩
    have ha : 0 < a := by linarith
    have hm : 0 < (p * a) ^ 2 := by positivity
    have hk' : 0 < k' := by nlinarith
    have hb0 : 0 < b := by nlinarith
    have hc0 : 0 < c := by nlinarith
    exact ⟨a, b, c, ha, hb0, hc0,
      certificate_sound p R a (p * a) k k' b c (ne_of_gt hR) ha4 rfl hkk'
        hb.symm hc.symm⟩
  · rintro ⟨a, b, c, ha, hb, hc, heq⟩
    rcases le_total a b with h1 | h1 <;> rcases le_total b c with h2 | h2 <;>
      rcases le_total a c with h3 | h3
    · exact hasAdmissibleCertificate_of_ordered hp ha h1 h2 heq
    · exact hasAdmissibleCertificate_of_ordered hp ha h1 h2 heq
    · exact hasAdmissibleCertificate_of_ordered hp ha h3 h2
        (by linear_combination heq)
    · exact hasAdmissibleCertificate_of_ordered hp hc h3 h1
        (by linear_combination heq)
    · exact hasAdmissibleCertificate_of_ordered hp hb h1 h3
        (by linear_combination heq)
    · exact hasAdmissibleCertificate_of_ordered hp hb h2 h3
        (by linear_combination heq)
    · exact hasAdmissibleCertificate_of_ordered hp hc h2 h1
        (by linear_combination heq)
    · exact hasAdmissibleCertificate_of_ordered hp hc h2 h1
        (by linear_combination heq)

/-! ### Proposition 2.1: the character obstruction -/

/-- **Proposition 2.1 (character obstruction).** Let `r ∣ R` be a prime
with `r ≡ 3 (mod 4)`. If every prime factor `q` of `m = p·a` is a
quadratic residue mod `r` (`(q | r) = +1`), then no divisor `k` of
`m²` lies in the class `−m (mod R)` — the residual `R` fails at `p`.

Every divisor of `m²` inherits symbol `+1` by multiplicative closure
(`divisor_jacobiSym_one`, reused from `Ladder.lean`), while the target
class has `(−m | r) = (−1 | r)·(m | r) = −1` because `r ≡ 3 (mod 4)`.
This is the Legendre special case of Lemma N (`jacobi_necessity`), and
it is *stronger* in that the character condition is imposed only at one
prime divisor `r` of `R`. -/
theorem character_obstruction {p a R r : ℕ} [Fact r.Prime]
    (hr4 : r % 4 = 3) (hrR : r ∣ R) (hm0 : p * a ≠ 0)
    (hfac : ∀ q : ℕ, q.Prime → q ∣ p * a → legendreSym r q = 1) :
    ∀ k : ℕ, k ∣ (p * a) ^ 2 → ¬ (R ∣ k + p * a) := by
  have hr_odd : Odd r := Nat.odd_iff.mpr (by omega)
  -- restate the hypothesis as a Jacobi condition, so the closure lemma applies
  have hfacJ : ∀ q : ℕ, q.Prime → q ∣ p * a → jacobiSym (q : ℤ) r = 1 := by
    intro q hq hd
    rw [← jacobiSym.legendreSym.to_jacobiSym r (q : ℤ)]
    exact hfac q hq hd
  have hm2 : (p * a) ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hall : ∀ q : ℕ, q.Prime → q ∣ (p * a) ^ 2 → jacobiSym (q : ℤ) r = 1 :=
    fun q hq hd => hfacJ q hq (hq.dvd_of_dvd_pow hd)
  have hdiv : ∀ n, n ∣ (p * a) ^ 2 → jacobiSym (n : ℤ) r = 1 :=
    divisor_jacobiSym_one hm2 hall
  have hmr : jacobiSym ((p * a : ℕ) : ℤ) r = 1 :=
    hdiv (p * a) (dvd_pow_self _ (by norm_num))
  have htarget : jacobiSym (-((p * a : ℕ) : ℤ)) r = -1 := by
    rw [jacobiSym.neg _ hr_odd, hmr, mul_one, ZMod.χ₄_nat_three_mod_four hr4]
  intro k hk hRk
  have hrk : (r : ℤ) ∣ (k : ℤ) + ((p * a : ℕ) : ℤ) := by
    have h : r ∣ k + p * a := dvd_trans hrR hRk
    exact_mod_cast h
  have hcong : (k : ℤ) ≡ -((p * a : ℕ) : ℤ) [ZMOD (r : ℤ)] :=
    Int.modEq_iff_dvd.mpr
      (by rw [show -((p * a : ℕ) : ℤ) - k = -((k : ℤ) + ((p * a : ℕ) : ℤ)) by
                ring]
          exact dvd_neg.mpr hrk)
  have h1 : jacobiSym (k : ℤ) r = 1 := hdiv k hk
  have h2 : jacobiSym (k : ℤ) r = -1 := by
    rw [jacobiSym.mod_left'
      (show (k : ℤ) % r = -((p * a : ℕ) : ℤ) % r from hcong), htarget]
  rw [h1] at h2
  norm_num at h2

/-! ### Proposition 2.2: guaranteed-success classes -/

/-- An odd residual is coprime to `4` (needed to divide the defining
congruence of the class `−4⁻¹` by `4`). -/
theorem isCoprime_four_of_odd {R : ℤ} (hR : R % 2 = 1) :
    IsCoprime R (4 : ℤ) := by
  obtain ⟨t, ht⟩ : ∃ t, R = 2 * t + 1 := ⟨R / 2, by omega⟩
  exact ⟨R, -(t ^ 2 + t), by rw [ht]; ring⟩

/-- **Proposition 2.2 (guaranteed-success classes).** Write
`t ≡ −4⁻¹p² ≡ −m (mod R)` for the target class. If `a` has a factor
`q > 0` with `q ≡ t·p^{−i} (mod R)` for some `i ≤ 2` — stated without
inverses as `R ∣ q·p^i + m`, i.e. `q·p^i ≡ −m` — then `k = q·p^i`
is a certificate: it divides `m²`, its cofactor `k' = m²/k` lies in
the same class, and the recovery formulae give **positive** integers
`b, c` solving the Erdős–Straus identity.

Integrality of `c` is `certificate_integrality` (from `k ≡ −m` and
`gcd(R, m) = 1`, which the paper notes is automatic since
`4a = p + R`); the identity itself is `certificate_sound`. -/
theorem success_class_certificate {p R a q m : ℤ} {i : ℕ}
    (hR : 0 < R) (hp : 0 < p) (ha : 0 < a) (hq : 0 < q) (hi : i ≤ 2)
    (ha4 : 4 * a = p + R) (hm : m = p * a) (hcop : IsCoprime R m)
    (hqa : q ∣ a) (hcls : R ∣ q * p ^ i + m) :
    (q * p ^ i) ∣ m ^ 2 ∧
      ∃ k' b c : ℤ, 0 < k' ∧ (q * p ^ i) * k' = m ^ 2 ∧
        R * b = q * p ^ i + m ∧ R * c = k' + m ∧ 0 < b ∧ 0 < c ∧
        4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  obtain ⟨s, hs⟩ := hqa
  have hs0 : 0 < s := by nlinarith
  have hpi : p ^ i * p ^ (2 - i) = p ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hm0 : 0 < m := by rw [hm]; positivity
  have hk0 : 0 < q * p ^ i := by positivity
  have hk'0 : 0 < p ^ (2 - i) * q * s ^ 2 := by positivity
  -- the explicit cofactor
  have hkk' : (q * p ^ i) * (p ^ (2 - i) * q * s ^ 2) = m ^ 2 := by
    have hmq : m = p * (q * s) := by rw [hm, hs]
    rw [hmq]
    calc q * p ^ i * (p ^ (2 - i) * q * s ^ 2)
        = (p ^ i * p ^ (2 - i)) * (q ^ 2 * s ^ 2) := by ring
      _ = p ^ 2 * (q ^ 2 * s ^ 2) := by rw [hpi]
      _ = (p * (q * s)) ^ 2 := by ring
  refine ⟨⟨_, hkk'.symm⟩, p ^ (2 - i) * q * s ^ 2, ?_⟩
  -- `b` from the class condition, `c` from integrality
  obtain ⟨b, hb⟩ := hcls
  have hcopk : IsCoprime R (q * p ^ i) :=
    (hcop.pow_right (n := 2)).of_isCoprime_of_dvd_right ⟨_, hkk'.symm⟩
  obtain ⟨c, hc⟩ :=
    certificate_integrality R m (q * p ^ i) (p ^ (2 - i) * q * s ^ 2) hkk'
      ⟨b, hb⟩ hcopk
  have hb0 : 0 < b := by nlinarith
  have hc0 : 0 < c := by nlinarith
  exact ⟨b, c, hk'0, hkk', hb.symm, hc.symm, hb0, hc0,
    certificate_sound p R a m (q * p ^ i) (p ^ (2 - i) * q * s ^ 2) b c
      (ne_of_gt hR) ha4 hm hkk' hb.symm hc.symm⟩

/-- **Proposition 2.2, the `p`-free clause.** A factor `q` of `a` in
the *fixed* class `−4⁻¹ (mod R)` — stated without inverses as
`R ∣ 4q + 1` — certifies success at `R` regardless of `p`: it is the
case `i = 2` of `success_class_certificate`, because
`t·p^{−2} ≡ −4⁻¹`. -/
theorem success_class_minus_quarter {p R a q m : ℤ}
    (hR : 0 < R) (hRodd : R % 2 = 1) (hp : 0 < p) (ha : 0 < a) (hq : 0 < q)
    (ha4 : 4 * a = p + R) (hm : m = p * a) (hcop : IsCoprime R m)
    (hqa : q ∣ a) (hcl : R ∣ 4 * q + 1) :
    (q * p ^ 2) ∣ m ^ 2 ∧
      ∃ k' b c : ℤ, 0 < k' ∧ (q * p ^ 2) * k' = m ^ 2 ∧
        R * b = q * p ^ 2 + m ∧ R * c = k' + m ∧ 0 < b ∧ 0 < c ∧
        4 * (a * b * c) = p * (b * c + a * c + a * b) := by
  have hcls : R ∣ q * p ^ 2 + m := by
    have h4 : 4 * (q * p ^ 2 + m) = (4 * q + 1) * p ^ 2 + p * R := by
      subst hm; linear_combination p * ha4
    have hdvd4 : R ∣ 4 * (q * p ^ 2 + m) := by
      rw [h4]
      exact dvd_add (Dvd.dvd.mul_right hcl _) (Dvd.intro_left p rfl)
    exact (isCoprime_four_of_odd hRodd).dvd_of_dvd_mul_left hdvd4
  exact success_class_certificate (i := 2) hR hp ha hq (le_refl 2) ha4 hm hcop
    hqa hcls

end ErdosStraus

-- Audit: these must report only standard axioms (no `sorryAx`, no
-- `native_decide` — this layer is fully symbolic).
#print axioms ErdosStraus.erdosStraus_rat_iff
#print axioms ErdosStraus.ordered_denominator_bounds
#print axioms ErdosStraus.residual_three_mod_four
#print axioms ErdosStraus.completeness
#print axioms ErdosStraus.hasAdmissibleCertificate_iff
#print axioms ErdosStraus.character_obstruction
#print axioms ErdosStraus.isCoprime_four_of_odd
#print axioms ErdosStraus.success_class_certificate
#print axioms ErdosStraus.success_class_minus_quarter
