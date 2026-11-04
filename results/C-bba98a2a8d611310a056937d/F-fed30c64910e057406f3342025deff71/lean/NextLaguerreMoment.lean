import CenteredSecondCoefficient
import PochhammerDifference

noncomputable section

namespace PartitionLaguerre

open Polynomial

def centeredPochhammer (q : ℕ) : ℚ[X] :=
  (descPochhammer ℚ (q + 2)).comp (X + C ((q + 1 : ℚ) / 2))

theorem centered_pochhammer_data (q : ℕ) :
    (centeredPochhammer q).natDegree = q + 2 ∧
      (centeredPochhammer q).leadingCoeff = 1 ∧
      (centeredPochhammer q).coeff q = -(q + 2 : ℚ) * (q + 1 : ℚ) * (q + 3 : ℚ) / 24 := by
  refine ⟨?_, ?_, centered_desc_second_coefficient q⟩
  · simp [centeredPochhammer, Polynomial.natDegree_comp]
  · rw [centeredPochhammer, Polynomial.leadingCoeff_comp (by simp),
      (monic_descPochhammer ℚ (q + 2)), Polynomial.leadingCoeff_X_add_C]
    simp

theorem centered_pochhammer_even (d : ℕ) :
    (centeredPochhammer (2 * d)).comp (C (-1) * X) = centeredPochhammer (2 * d) := by
  apply polynomial_eq_of_nat_eval
  intro n
  simp only [centeredPochhammer, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h := desc_pochhammer_eval_reflection (2 * d + 2)
    ((n : ℚ) + (2 * d + 1 : ℚ) / 2)
  have ha : ((2 * d + 2 : ℕ) : ℚ) - 1 - ((n : ℚ) + (2 * d + 1 : ℚ) / 2) =
      (-1 : ℚ) * (n : ℚ) + (2 * d + 1 : ℚ) / 2 := by push_cast; ring
  have he : Even (2 * d + 2) := ⟨d + 1, by omega⟩
  rw [ha, he.neg_one_pow, one_mul] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

theorem centered_pochhammer_next_zero (d : ℕ) :
    (centeredPochhammer (2 * d)).coeff (2 * d + 1) = 0 := by
  have h := congrArg (fun P : ℚ[X] => P.coeff (2 * d + 1)) (centered_pochhammer_even d)
  have ho : Odd (2 * d + 1) := ⟨d, by omega⟩
  rw [Polynomial.comp_C_mul_X_coeff, ho.neg_one_pow] at h
  linarith

def nextMomentResidual (d : ℕ) : ℚ[X] :=
  centeredPochhammer (2 * d) - X ^ (2 * d + 2) -
    C ((centeredPochhammer (2 * d)).coeff (2 * d)) * X ^ (2 * d)

theorem next_moment_residual_degree (d : ℕ) (hd : 1 ≤ d) :
    (nextMomentResidual d).natDegree < 2 * d := by
  let q := 2 * d
  let P := centeredPochhammer q
  have hP := centered_pochhammer_data q
  have htop : P.coeff (q + 2) = 1 := by
    rw [← hP.1, Polynomial.coeff_natDegree, hP.2.1]
  have hnext : P.coeff (q + 1) = 0 := centered_pochhammer_next_zero d
  have hbound : (nextMomentResidual d).natDegree ≤ q + 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro h hh
    have hp : P.coeff h = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1]; exact hh)
    simp only [nextMomentResidual, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    change P.coeff h - (X ^ (q + 2) : ℚ[X]).coeff h - P.coeff q * (X ^ q : ℚ[X]).coeff h = 0
    rw [hp, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow,
      if_neg (by omega), if_neg (by omega)]
    ring
  have hz0 : (nextMomentResidual d).coeff q = 0 := by
    simp only [nextMomentResidual, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    change P.coeff q - (X ^ (q + 2) : ℚ[X]).coeff q - P.coeff q * (X ^ q : ℚ[X]).coeff q = 0
    rw [Polynomial.coeff_X_pow, if_neg (by omega), Polynomial.coeff_X_pow_self]
    ring
  have hz1 : (nextMomentResidual d).coeff (q + 1) = 0 := by
    simp only [nextMomentResidual, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    change P.coeff (q + 1) - (X ^ (q + 2) : ℚ[X]).coeff (q + 1) -
      P.coeff q * (X ^ q : ℚ[X]).coeff (q + 1) = 0
    rw [hnext, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow,
      if_neg (by omega), if_neg (by omega)]
    ring
  have hz2 : (nextMomentResidual d).coeff (q + 2) = 0 := by
    simp only [nextMomentResidual, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    change P.coeff (q + 2) - (X ^ (q + 2) : ℚ[X]).coeff (q + 2) -
      P.coeff q * (X ^ q : ℚ[X]).coeff (q + 2) = 0
    rw [htop, Polynomial.coeff_X_pow_self, Polynomial.coeff_X_pow, if_neg (by omega)]
    ring
  have hsmall : (nextMomentResidual d).natDegree ≤ q - 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro h hh
    by_cases hlarge : q + 2 < h
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hbound.trans_lt hlarge)
    · have hc : h = q ∨ h = q + 1 ∨ h = q + 2 := by dsimp [q] at *; omega
      rcases hc with rfl | rfl | rfl
      · exact hz0
      · exact hz1
      · exact hz2
  exact hsmall.trans_lt (by dsimp [q]; omega)

theorem centered_pochhammer_weighted_value (d : ℕ) :
    (∑ k ∈ Finset.range (2 * d + 1), laguerreWeight d k *
      (centeredPochhammer (2 * d)).eval ((k : ℚ) - (d : ℚ))) =
        (-1 : ℚ) ^ d * (-((2 * d + 2).factorial : ℚ) / 8) := by
  let q := 2 * d
  let c : ℚ := (q + 1 : ℚ) / 2
  have hfun : (centeredPochhammer q).eval =
      fun x : ℚ => (descPochhammer ℚ (q + 2)).eval (x + c) := by
    funext x
    simp only [centeredPochhammer, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    rfl
  have harg : -(d : ℚ) + c = 1 / 2 := by dsimp [c, q]; push_cast; ring
  have htwo : (descPochhammer ℚ 2).eval (1 / 2) = -1 / 4 := by
    norm_num [descPochhammer_succ_eval, descPochhammer_zero]
  have hD : ((fwdDiff (1 : ℚ))^[q]) (centeredPochhammer q).eval (-(d : ℚ)) =
      -((q + 2).factorial : ℚ) / 8 := by
    rw [hfun, fwdDiff_iter_comp_add (1 : ℚ) (descPochhammer ℚ (q + 2)).eval c q (-(d : ℚ)), harg]
    have h := congrFun (desc_pochhammer_iterated_difference 2 q) (1 / 2 : ℚ)
    simp only [show 2 + q = q + 2 by omega, Pi.smul_apply, smul_eq_mul] at h
    calc
      _ = (((q + 2).factorial : ℚ) / 2) * (descPochhammer ℚ 2).eval (1 / 2) := by
        simpa only [show ((2 : ℕ).factorial : ℚ) = 2 by norm_num] using h
      _ = _ := by rw [htwo]; ring
  have hw := laguerre_weighted_polynomial_sum d (centeredPochhammer q) (-(d : ℚ))
  have ha (k : ℕ) : -(d : ℚ) + (k : ℚ) = (k : ℚ) - (d : ℚ) := by ring
  simp only [ha] at hw
  rw [hD] at hw
  exact hw

/-- The next even moment needed by the odd critical coefficient. -/
theorem laguerre_moment_next_even (d : ℕ) (hd : 1 ≤ d) :
    laguerreMoment d (2 * d + 2) =
      (-1 : ℚ) ^ d * ((2 * d + 2).factorial : ℚ) * (d : ℚ) / 12 := by
  let q := 2 * d
  let P := centeredPochhammer q
  let R := nextMomentResidual d
  let c := P.coeff q
  have hR := next_moment_residual_degree d hd
  have hzero : ((fwdDiff (1 : ℚ))^[q]) R.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hR
  have hw := laguerre_weighted_polynomial_sum d R (-(d : ℚ))
  rw [hzero] at hw
  have ha (k : ℕ) : -(d : ℚ) + (k : ℚ) = (k : ℚ) - (d : ℚ) := by ring
  simp only [ha, Pi.zero_apply, mul_zero] at hw
  have heval (x : ℚ) : P.eval x = R.eval x + x ^ (q + 2) + c * x ^ q := by
    dsimp [R]
    simp only [nextMomentResidual, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change P.eval x = (P.eval x - x ^ (q + 2) - c * x ^ q) + x ^ (q + 2) + c * x ^ q
    ring
  have hsplit : (∑ k ∈ Finset.range (2 * d + 1),
      laguerreWeight d k * P.eval ((k : ℚ) - (d : ℚ))) =
      (∑ k ∈ Finset.range (2 * d + 1), laguerreWeight d k * R.eval ((k : ℚ) - (d : ℚ))) +
        laguerreMoment d (q + 2) + c * laguerreMoment d q := by
    simp only [laguerreMoment, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [heval]
    ring
  rw [hw, zero_add] at hsplit
  have hp := centered_pochhammer_weighted_value d
  have hm : laguerreMoment d q = (-1 : ℚ) ^ d * (q.factorial : ℚ) := laguerre_moment_at_order d
  have hc : c = -(q + 2 : ℚ) * (q + 1 : ℚ) * (q + 3 : ℚ) / 24 := (centered_pochhammer_data q).2.2
  have hfact : ((2 * d + 2).factorial : ℚ) =
      (2 * (d : ℚ) + 2) * (2 * (d : ℚ) + 1) * ((2 * d).factorial : ℚ) := by
    rw [show 2 * d + 2 = (2 * d + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  calc
    _ = (-1 : ℚ) ^ d * (-((2 * d + 2).factorial : ℚ) / 8) - c *
        ((-1 : ℚ) ^ d * ((2 * d).factorial : ℚ)) := by
      rw [hp, hm] at hsplit
      linarith
    _ = _ := by
      rw [hc, hfact]
      dsimp [q]
      push_cast
      ring

end PartitionLaguerre

#print axioms PartitionLaguerre.centered_pochhammer_data
#print axioms PartitionLaguerre.centered_pochhammer_even
#print axioms PartitionLaguerre.centered_pochhammer_next_zero
#print axioms PartitionLaguerre.next_moment_residual_degree
#print axioms PartitionLaguerre.centered_pochhammer_weighted_value
#print axioms PartitionLaguerre.laguerre_moment_next_even
