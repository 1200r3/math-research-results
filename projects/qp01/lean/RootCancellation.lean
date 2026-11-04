import Statement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem solution : formalStatement := by
  intro z d hz h_one
  have h_sub : (1 - z : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h_one)
  have h_basic : (2 - z - z⁻¹ : ℂ) = (-1 : ℂ) * (1 - z) ^ 2 / z := by
    field_simp [hz]
    <;> ring
  rw [h_basic, div_pow, mul_pow, ← pow_mul]
  field_simp [hz, h_sub]

#print axioms solution
