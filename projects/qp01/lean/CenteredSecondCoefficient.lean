import CenteredPolynomial
import ShiftTopCoefficients

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem centered_desc_second_coefficient (k : ℕ) :
    ((descPochhammer ℚ (k + 2)).comp (X + C ((k + 1 : ℚ) / 2))).coeff k =
      -(k + 2 : ℚ) * (k + 1 : ℚ) * (k + 3 : ℚ) / 24 := by
  rw [shift_coefficient_two_below _ k _ (by simp), desc_pochhammer_second_at,
    desc_pochhammer_next_at (k + 1), (monic_descPochhammer ℚ (k + 2))]
  push_cast
  ring

theorem centered_polynomial_degree_leading (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (centeredPolynomialPart d m).natDegree = 2 * d ∧
      (centeredPolynomialPart d m).leadingCoeff =
        1 / ((m : ℚ) * ((2 * d).factorial : ℚ)) := by
  have h := concrete_polynomial_part_degree_leading d m hd hm
  constructor
  · rw [centeredPolynomialPart, Polynomial.natDegree_comp, Polynomial.natDegree_sub_C,
      Polynomial.natDegree_X, mul_one, h.1]
  · rw [centeredPolynomialPart, Polynomial.leadingCoeff_comp (by simp),
      Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one, h.2]

theorem centered_polynomial_half_difference (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (centeredPolynomialPart d m).comp (X + C ((m : ℚ) / 2)) -
      (centeredPolynomialPart d m).comp (X + C (-((m : ℚ) / 2))) =
      C (((2 * d - 1).factorial : ℚ)⁻¹) *
        (descPochhammer ℚ (2 * d - 1)).comp (X + C ((2 * (d : ℚ) - 2) / 2)) := by
  apply polynomial_eq_of_nat_eval
  intro n
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
  have h := centered_polynomial_step d m hm ((n : ℚ) - (m : ℚ) / 2)
  rw [show (n : ℚ) - (m : ℚ) / 2 + (m : ℚ) = (n : ℚ) + (m : ℚ) / 2 by ring] at h
  have harg : ((n : ℚ) - (m : ℚ) / 2) - partitionCenter d m + (m : ℚ) +
      ((2 * d - 1 : ℕ) : ℚ) = (n : ℚ) + (2 * (d : ℚ) - 2) / 2 := by
    rw [Nat.cast_sub (show 1 ≤ 2 * d by omega)]
    simp only [partitionCenter, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [harg] at h
  rw [show (n : ℚ) + -((m : ℚ) / 2) = (n : ℚ) - (m : ℚ) / 2 by ring]
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem centered_second_coefficient_index (d m k : ℕ) (hd : 2 ≤ d) (hm : 0 < m)
    (hk : 2 * d = k + 3) :
    (centeredPolynomialPart d m).coeff (k + 1) =
      -(1 / ((m : ℚ) * ((2 * d).factorial : ℚ))) *
        (k + 3 : ℚ) * (k + 2 : ℚ) * ((k + 3 : ℚ) + (m : ℚ) ^ 2) / 24 := by
  let S := centeredPolynomialPart d m
  let a : ℚ := 1 / ((m : ℚ) * ((2 * d).factorial : ℚ))
  have hS := centered_polynomial_degree_leading d m (by omega) hm
  have hminus : 2 * d - 1 = k + 2 := by omega
  have hcast : 2 * (d : ℚ) = (k + 3 : ℚ) := by exact_mod_cast hk
  have hcenter : (2 * (d : ℚ) - 2) / 2 = (k + 1 : ℚ) / 2 := by rw [hcast]; ring
  have hcoef := congrArg (fun P : ℚ[X] => P.coeff k) (centered_polynomial_half_difference d m (by omega) hm)
  rw [symmetric_shift_third_coefficient S k ((m : ℚ) / 2) (hS.1.trans hk),
    Polynomial.coeff_C_mul, hminus, hcenter, centered_desc_second_coefficient,
    hS.2] at hcoef
  have hfact : ((2 * d).factorial : ℚ) = (k + 3 : ℚ) * ((k + 2).factorial : ℚ) := by
    rw [hk, show k + 3 = (k + 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hf : ((k + 2).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + 2)
  have hinv : ((k + 2).factorial : ℚ)⁻¹ = a * (m : ℚ) * (k + 3 : ℚ) := by
    dsimp [a]
    rw [hfact]
    field_simp <;> ring
  rw [hinv] at hcoef
  have hcancel : ((m : ℚ) * (k + 1 : ℚ)) *
      (S.coeff (k + 1) - (-a * (k + 3 : ℚ) * (k + 2 : ℚ) *
        ((k + 3 : ℚ) + (m : ℚ) ^ 2) / 24)) = 0 := by
    calc
      _ = (2 * ((m : ℚ) / 2) * (k + 1 : ℚ) * S.coeff (k + 1) +
          (((m : ℚ) / 2) ^ 3 / 3) * (k + 3 : ℚ) * (k + 2 : ℚ) * (k + 1 : ℚ) * a) -
        ((a * (m : ℚ) * (k + 3 : ℚ)) *
          (-(k + 2 : ℚ) * (k + 1 : ℚ) * (k + 3 : ℚ) / 24)) := by ring
      _ = 0 := sub_eq_zero.mpr hcoef
  have hnonzero : (m : ℚ) * (k + 1 : ℚ) ≠ 0 := mul_ne_zero hmQ (by positivity)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hnonzero)

theorem centered_polynomial_second_coefficient (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) :
    (centeredPolynomialPart d m).coeff (2 * d - 2) =
      -(1 / ((m : ℚ) * ((2 * d).factorial : ℚ))) *
        (2 * (d : ℚ)) * (2 * (d : ℚ) - 1) * (2 * (d : ℚ) + (m : ℚ) ^ 2) / 24 := by
  have h := centered_second_coefficient_index d m (2 * d - 3) hd hm (by omega)
  rw [show 2 * d - 3 + 1 = 2 * d - 2 by omega] at h
  rw [Nat.cast_sub (show 3 ≤ 2 * d by omega)] at h
  push_cast at h
  convert h using 1 <;> ring

end PartitionLaguerre

#print axioms PartitionLaguerre.centered_desc_second_coefficient
#print axioms PartitionLaguerre.centered_polynomial_degree_leading
#print axioms PartitionLaguerre.centered_polynomial_half_difference
#print axioms PartitionLaguerre.centered_second_coefficient_index
#print axioms PartitionLaguerre.centered_polynomial_second_coefficient
