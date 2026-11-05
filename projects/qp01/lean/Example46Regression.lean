import ConcreteLeadingCoefficient

namespace PartitionLaguerre

/-- Example 4.6 uses half of the full second-order transform.
This regression specializes the already verified general coefficient identity. -/
theorem example46_half_transform_coefficient (r : ℕ) :
    (residueTransform 300 2 (concreteResiduePolynomial 2 300) r).coeff 4 / 2 =
      if 300 ∣ r + 4 then (151 / 1080000 : ℚ) else (1 / 1080000 : ℚ) := by
  rw [concrete_transform_boundary_coefficient 2 300 r (by decide) (by decide)]
  rw [show Nat.centralBinom 2 = 6 by decide]
  change ((1 / ((300 : ℚ) * 24)) ^ 2 * 24 * 6 +
      2 * (1 / ((300 : ℚ) * 24)) * (-1 : ℚ) ^ 2 *
        ((if 300 ∣ r + 4 then 1 else 0) - 1 / (300 : ℚ))) / 2 =
        if 300 ∣ r + 4 then (151 / 1080000 : ℚ) else (1 / 1080000 : ℚ)
  split_ifs <;> norm_num

example : (residueTransform 300 2 (concreteResiduePolynomial 2 300) 296).coeff 4 / 2 =
    (151 / 1080000 : ℚ) := by
  simpa only [if_pos (by decide : 300 ∣ 296 + 4)] using example46_half_transform_coefficient 296

example : (residueTransform 300 2 (concreteResiduePolynomial 2 300) 297).coeff 4 / 2 =
    (1 / 1080000 : ℚ) := by
  simpa only [if_neg (by decide : ¬ 300 ∣ 297 + 4)] using example46_half_transform_coefficient 297

end PartitionLaguerre

#print axioms PartitionLaguerre.example46_half_transform_coefficient
