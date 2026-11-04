import PolynomialPartDegree
import Mathlib.Algebra.Polynomial.Monic

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem shift_polynomial_coefficient (P : ℚ[X]) (c : ℚ) (h : ℕ) :
    (P.comp (X + C c)).coeff h =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        P.coeff i * (c ^ (i - h) * (i.choose h : ℚ)) := by
  have heq : P.comp (X + C c) =
      ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i) * (X + C c) ^ i :=
    Polynomial.eval₂_eq_sum_range Polynomial.C (X + C c)
  rw [heq]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]

theorem desc_pochhammer_next_coefficient (k : ℕ) :
    (descPochhammer ℚ k).nextCoeff = -(k : ℚ) * ((k : ℚ) - 1) / 2 := by
  induction k with
  | zero => simp [descPochhammer_zero, Polynomial.nextCoeff]
  | succ k ih =>
    rw [descPochhammer_succ_right, ← Polynomial.C_eq_natCast,
      (monic_descPochhammer ℚ k).nextCoeff_mul (monic_X_sub_C (k : ℚ)),
      ih, Polynomial.nextCoeff_X_sub_C]
    push_cast
    ring

theorem desc_pochhammer_next_at (k : ℕ) :
    (descPochhammer ℚ (k + 1)).coeff k = -(k + 1 : ℚ) * (k : ℚ) / 2 := by
  have h := desc_pochhammer_next_coefficient (k + 1)
  simp only [Polynomial.nextCoeff, descPochhammer_natDegree, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
  convert h using 1 <;> ring

theorem desc_pochhammer_second_at (k : ℕ) :
    (descPochhammer ℚ (k + 2)).coeff k =
      (k + 2 : ℚ) * (k + 1 : ℚ) * (k : ℚ) * (3 * (k : ℚ) + 5) / 24 := by
  induction k with
  | zero =>
    norm_num [descPochhammer_succ_right, descPochhammer_zero]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, descPochhammer_succ_right,
      mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
      Polynomial.coeff_mul_natCast, ih, desc_pochhammer_next_at (k + 1)]
    push_cast
    ring

end PartitionLaguerre

#print axioms PartitionLaguerre.shift_polynomial_coefficient
#print axioms PartitionLaguerre.desc_pochhammer_next_coefficient
#print axioms PartitionLaguerre.desc_pochhammer_next_at
#print axioms PartitionLaguerre.desc_pochhammer_second_at
