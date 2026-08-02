import Mathlib.Tactic
#check @ZMod.inv_eq_of_mul_eq_one
example : -(4⁻¹ : ZMod 19) = 2 ^ 7 := by
  rw [ZMod.inv_eq_of_mul_eq_one 19 4 5 (by decide)]
  decide
