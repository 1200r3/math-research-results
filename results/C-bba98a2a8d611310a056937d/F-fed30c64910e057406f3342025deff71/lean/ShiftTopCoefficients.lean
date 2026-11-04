import PolynomialTopCoefficients

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem cast_choose_add_one (k : ℕ) :
    (((k + 1).choose k : ℕ) : ℚ) = (k + 1 : ℚ) := by
  exact_mod_cast Nat.choose_succ_self_right k

theorem cast_choose_add_two (k : ℕ) :
    (((k + 2).choose k : ℕ) : ℚ) = (k + 2 : ℚ) * (k + 1 : ℚ) / 2 := by
  rw [← Nat.choose_symm (show k ≤ k + 2 by omega), show k + 2 - k = 2 by omega,
    Nat.cast_choose_eq_descPochhammer_div ℚ]
  norm_num [descPochhammer_succ_eval, descPochhammer_zero, Nat.factorial] <;>
    push_cast <;> ring <;> simp

theorem cast_choose_add_three (k : ℕ) :
    (((k + 3).choose k : ℕ) : ℚ) =
      (k + 3 : ℚ) * (k + 2 : ℚ) * (k + 1 : ℚ) / 6 := by
  rw [← Nat.choose_symm (show k ≤ k + 3 by omega), show k + 3 - k = 3 by omega,
    Nat.cast_choose_eq_descPochhammer_div ℚ]
  norm_num [descPochhammer_succ_eval, descPochhammer_zero, Nat.factorial] <;>
    push_cast <;> ring <;> simp

theorem shift_coefficient_prefix_zero (P : ℚ[X]) (c : ℚ) (k : ℕ) :
    (∑ i ∈ Finset.range k, P.coeff i * (c ^ (i - k) * (i.choose k : ℚ))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi), Nat.cast_zero, mul_zero, mul_zero]

theorem shift_coefficient_two_below (P : ℚ[X]) (k : ℕ) (c : ℚ)
    (hP : P.natDegree = k + 2) :
    (P.comp (X + C c)).coeff k = P.coeff k +
      (k + 1 : ℚ) * c * P.coeff (k + 1) +
      ((k + 2 : ℚ) * (k + 1 : ℚ) / 2) * c ^ 2 * P.leadingCoeff := by
  have htop : P.coeff (k + 2) = P.leadingCoeff := by
    rw [← hP, Polynomial.coeff_natDegree]
  rw [shift_polynomial_coefficient, hP]
  repeat rw [Finset.sum_range_succ]
  rw [shift_coefficient_prefix_zero]
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, pow_one,
    Nat.choose_self, Nat.cast_one, mul_one, zero_add]
  rw [cast_choose_add_one, cast_choose_add_two, htop]
  ring

theorem symmetric_shift_third_coefficient (P : ℚ[X]) (k : ℕ) (c : ℚ)
    (hP : P.natDegree = k + 3) :
    (P.comp (X + C c) - P.comp (X + C (-c))).coeff k =
      2 * c * (k + 1 : ℚ) * P.coeff (k + 1) +
      (c ^ 3 / 3) * (k + 3 : ℚ) * (k + 2 : ℚ) * (k + 1 : ℚ) * P.leadingCoeff := by
  have htop : P.coeff (k + 3) = P.leadingCoeff := by
    rw [← hP, Polynomial.coeff_natDegree]
  rw [Polynomial.coeff_sub, shift_polynomial_coefficient, shift_polynomial_coefficient, hP]
  repeat rw [Finset.sum_range_succ]
  rw [shift_coefficient_prefix_zero, shift_coefficient_prefix_zero]
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, pow_one,
    Nat.choose_self, Nat.cast_one, mul_one, zero_add]
  rw [cast_choose_add_one, cast_choose_add_three, htop]
  ring

end PartitionLaguerre

#print axioms PartitionLaguerre.cast_choose_add_one
#print axioms PartitionLaguerre.cast_choose_add_two
#print axioms PartitionLaguerre.cast_choose_add_three
#print axioms PartitionLaguerre.shift_coefficient_prefix_zero
#print axioms PartitionLaguerre.shift_coefficient_two_below
#print axioms PartitionLaguerre.symmetric_shift_third_coefficient
