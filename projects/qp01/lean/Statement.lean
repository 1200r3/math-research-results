import Mathlib.Data.Complex.Basic

def formalStatement : Prop :=
  ∀ (z : ℂ) (d : ℕ), z ≠ 0 → z ≠ 1 →
    (2 - z - z⁻¹) ^ d / (1 - z) ^ (2 * d) =
      (-1 : ℂ) ^ d / z ^ d
