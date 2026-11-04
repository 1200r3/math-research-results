import CriticalPeriodicMoments
import ShiftTopCoefficients
import SmoothPolynomial

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem shift_coefficient_one_below (P : ℚ[X]) (k : ℕ) (c : ℚ)
    (hP : P.natDegree = k + 1) :
    (P.comp (X + C c)).coeff k = P.coeff k + (k + 1 : ℚ) * c * P.leadingCoeff := by
  have htop : P.coeff (k + 1) = P.leadingCoeff := by rw [← hP, Polynomial.coeff_natDegree]
  rw [shift_polynomial_coefficient, hP]
  repeat rw [Finset.sum_range_succ]
  rw [shift_coefficient_prefix_zero]
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, pow_zero, pow_one,
    Nat.choose_self, Nat.cast_one, mul_one, zero_add]
  rw [cast_choose_add_one, htop]
  ring

theorem reflected_periodic_centered_moment (m d r h : ℕ) (b : ℕ → ℚ) :
    (∑ k ∈ Finset.range (2 * d + 1), laguerreWeight d k *
      ((k : ℚ) - (d : ℚ)) ^ h * b ((r + (2 * d - k)) % m)) =
      (-1 : ℚ) ^ h * periodicCenteredMoment d h (fun n => b (n % m)) r := by
  conv_lhs => rw [← Finset.sum_range_reflect]
  rw [periodicCenteredMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * d := by have := Finset.mem_range.mp hk; omega
  have he : 2 * d + 1 - 1 - k = 2 * d - k := by omega
  have ha : ((2 * d - k : ℕ) : ℚ) - (d : ℚ) = -((k : ℚ) - (d : ℚ)) := by
    rw [Nat.cast_sub hk']
    push_cast
    ring
  rw [he, laguerre_weight_reflect d k hk', Nat.sub_sub_self hk', ha, neg_pow]
  ring

theorem smooth_polynomial_pair_even (j : ℕ) (P : ℚ[X])
    (heven : P.comp (C (-1) * X) = P) :
    (smoothPolynomialPair j P P).comp (C (-1) * X) = smoothPolynomialPair j P P := by
  have hP (x : ℚ) : P.eval (-x) = P.eval x := by
    have h := congrArg (fun Q : ℚ[X] => Q.eval x) heven
    simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, neg_one_mul] using h
  have hEval (x : ℚ) : (smoothPolynomialPair j P P).eval x =
      ∑ k ∈ Finset.range (2 * j + 1), laguerreWeight j k *
        P.eval (x + ((k : ℚ) - (j : ℚ))) * P.eval (x - ((k : ℚ) - (j : ℚ))) := by
    rw [smooth_polynomial_pair_formula]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X]
  apply polynomial_eq_of_nat_eval
  intro n
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, neg_one_mul]
  rw [hEval, hEval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show -(n : ℚ) + ((k : ℚ) - (j : ℚ)) = -((n : ℚ) - ((k : ℚ) - (j : ℚ))) by ring,
    show -(n : ℚ) - ((k : ℚ) - (j : ℚ)) = -((n : ℚ) + ((k : ℚ) - (j : ℚ))) by ring,
    hP, hP]
  ring

theorem smooth_polynomial_pair_odd_coefficient_zero (j i : ℕ) (P : ℚ[X])
    (heven : P.comp (C (-1) * X) = P) (hi : Odd i) :
    (smoothPolynomialPair j P P).coeff i = 0 := by
  have h := congrArg (fun Q : ℚ[X] => Q.coeff i) (smooth_polynomial_pair_even j P heven)
  rw [Polynomial.comp_C_mul_X_coeff, hi.neg_one_pow] at h
  linarith

end PartitionLaguerre

#print axioms PartitionLaguerre.shift_coefficient_one_below
#print axioms PartitionLaguerre.reflected_periodic_centered_moment
#print axioms PartitionLaguerre.smooth_polynomial_pair_even
#print axioms PartitionLaguerre.smooth_polynomial_pair_odd_coefficient_zero
