import CriticalCoefficientTools
import CenteredSecondCoefficient
import CriticalReduction

noncomputable section

namespace PartitionLaguerre

open Polynomial

def criticalCenterShift (d m : ℕ) : ℚ := (d : ℚ) + partitionCenter d m

def criticalCenteredTransform (d m r : ℕ) : ℚ[X] :=
  (residueTransform m d (concreteResiduePolynomial d m) r).comp
    (X - C (criticalCenterShift d m))

def centeredCrossPolynomial (m d : ℕ) (P : ℚ[X]) (b : ℕ → ℚ) (r : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (2 * d + 1), C (laguerreWeight d k) *
    (C (b ((r + k) % m)) * P.comp (X - C ((k : ℚ) - (d : ℚ))) +
      C (b ((r + (2 * d - k)) % m)) * P.comp (X + C ((k : ℚ) - (d : ℚ))))

theorem critical_centered_transform_formula (d m r : ℕ) (hm : 0 < m) :
    criticalCenteredTransform d m r =
      smoothPolynomialPair d (centeredPolynomialPart d m) (centeredPolynomialPart d m) +
      centeredCrossPolynomial m d (centeredPolynomialPart d m) (concretePeriodicConstant d m) r +
      C (periodicProductConstant m d (concretePeriodicConstant d m) r) := by
  let S := centeredPolynomialPart d m
  let b := concretePeriodicConstant d m
  have hF (s : ℕ) (y : ℚ) : (concreteResiduePolynomial d m s).eval y =
      S.eval (y + partitionCenter d m) + b s := by
    rw [concrete_residue_common_part d m s hm, Polynomial.eval_add, Polynomial.eval_C]
    have hS : S.eval (y + partitionCenter d m) = (concretePolynomialPart d m).eval y := by
      simp only [S, centeredPolynomialPart, Polynomial.eval_comp, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, add_sub_cancel_right]
    rw [hS]
    rfl
  apply polynomial_eq_of_nat_eval
  intro n
  simp only [criticalCenteredTransform, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [smooth_polynomial_pair_formula]
  unfold residueTransform centeredCrossPolynomial periodicProductConstant
  simp only [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_X, hF]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * d := by have := Finset.mem_range.mp hk; omega
  have ha : (n : ℚ) - criticalCenterShift d m + (k : ℚ) + partitionCenter d m =
      (n : ℚ) + ((k : ℚ) - (d : ℚ)) := by dsimp [criticalCenterShift]; ring
  have hb : (n : ℚ) - criticalCenterShift d m + ((2 * d - k : ℕ) : ℚ) + partitionCenter d m =
      (n : ℚ) - ((k : ℚ) - (d : ℚ)) := by
    rw [Nat.cast_sub hk']
    push_cast
    dsimp [criticalCenterShift]
    ring
  rw [ha, hb]
  change laguerreWeight d k * (S.eval ((n : ℚ) + ((k : ℚ) - (d : ℚ))) + b ((r + k) % m)) *
      (S.eval ((n : ℚ) - ((k : ℚ) - (d : ℚ))) + b ((r + (2 * d - k)) % m)) = _
  ring

theorem critical_centered_leading_eq (d m r : ℕ) :
    (criticalCenteredTransform d m r).leadingCoeff =
      (residueTransform m d (concreteResiduePolynomial d m) r).leadingCoeff := by
  rw [criticalCenteredTransform, Polynomial.leadingCoeff_comp (by simp),
    Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]

theorem critical_centered_degree_eq (d m r : ℕ) :
    (criticalCenteredTransform d m r).natDegree =
      (residueTransform m d (concreteResiduePolynomial d m) r).natDegree := by
  simp [criticalCenteredTransform, Polynomial.natDegree_comp]

theorem centered_cross_one_below (m d r k : ℕ) (P : ℚ[X]) (b : ℕ → ℚ)
    (hP : P.natDegree = k + 1) (hodd : P.coeff k = 0) :
    (centeredCrossPolynomial m d P b r).coeff k =
      -2 * (k + 1 : ℚ) * P.leadingCoeff *
        periodicCenteredMoment d 1 (fun n => b (n % m)) r := by
  have hneg (u : ℚ) : (X - C u : ℚ[X]) = X + C (-u) := by simp [sub_eq_add_neg]
  have href := reflected_periodic_centered_moment m d r 1 b
  simp only [pow_one] at href
  simp only [centeredCrossPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_add, hneg, shift_coefficient_one_below P k _ hP, hodd, zero_add]
  calc
    _ = -(k + 1 : ℚ) * P.leadingCoeff * periodicCenteredMoment d 1 (fun n => b (n % m)) r +
        (k + 1 : ℚ) * P.leadingCoeff *
          (∑ a ∈ Finset.range (2 * d + 1), laguerreWeight d a *
            ((a : ℚ) - (d : ℚ)) * b ((r + (2 * d - a)) % m)) := by
      simp only [periodicCenteredMoment, pow_one, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by rw [href]; ring

theorem centered_cross_two_below (m d r k : ℕ) (P : ℚ[X]) (b : ℕ → ℚ)
    (hP : P.natDegree = k + 2) (hodd : P.coeff (k + 1) = 0) :
    (centeredCrossPolynomial m d P b r).coeff k =
      2 * P.coeff k * periodicCenteredMoment d 0 (fun n => b (n % m)) r +
      (k + 2 : ℚ) * (k + 1 : ℚ) * P.leadingCoeff *
        periodicCenteredMoment d 2 (fun n => b (n % m)) r := by
  have hneg (u : ℚ) : (X - C u : ℚ[X]) = X + C (-u) := by simp [sub_eq_add_neg]
  have hshift (u : ℚ) : (P.comp (X + C u)).coeff k =
      P.coeff k + ((k + 2 : ℚ) * (k + 1 : ℚ) / 2) * u ^ 2 * P.leadingCoeff := by
    rw [shift_coefficient_two_below P k u hP, hodd, mul_zero, add_zero]
  have href0 := reflected_periodic_centered_moment m d r 0 b
  have href2 := reflected_periodic_centered_moment m d r 2 b
  simp only [pow_zero, pow_two, neg_one_mul, neg_mul, neg_neg, one_mul, mul_one] at href0 href2
  simp only [centeredCrossPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_add, hneg, hshift]
  let A : ℚ := (k + 2 : ℚ) * (k + 1 : ℚ) / 2 * P.leadingCoeff
  have hsum :
      (∑ a ∈ Finset.range (2 * d + 1),
        laguerreWeight d a *
          (b ((r + a) % m) * (P.coeff k + ((k + 2 : ℚ) * (k + 1 : ℚ) / 2) *
              (-((a : ℚ) - (d : ℚ))) ^ 2 * P.leadingCoeff) +
            b ((r + (2 * d - a)) % m) * (P.coeff k + ((k + 2 : ℚ) * (k + 1 : ℚ) / 2) *
              ((a : ℚ) - (d : ℚ)) ^ 2 * P.leadingCoeff))) =
      P.coeff k * (periodicCenteredMoment d 0 (fun n => b (n % m)) r +
        ∑ a ∈ Finset.range (2 * d + 1), laguerreWeight d a * b ((r + (2 * d - a)) % m)) +
      A * (periodicCenteredMoment d 2 (fun n => b (n % m)) r +
        ∑ a ∈ Finset.range (2 * d + 1), laguerreWeight d a * ((a : ℚ) - (d : ℚ)) ^ 2 *
          b ((r + (2 * d - a)) % m)) := by
    simp only [periodicCenteredMoment, pow_zero, mul_one, Finset.mul_sum,
      Finset.sum_add_distrib]
    repeat rw [← Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [A]
    ring
  rw [hsum, href0]
  have href2' : (∑ a ∈ Finset.range (2 * d + 1), laguerreWeight d a *
      ((a : ℚ) - (d : ℚ)) ^ 2 * b ((r + (2 * d - a)) % m)) =
      periodicCenteredMoment d 2 (fun n => b (n % m)) r := by
    simpa only [pow_two] using href2
  rw [href2']
  dsimp [A]
  ring

theorem concrete_periodic_zeroth_moment (d m n : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    periodicCenteredMoment d 0 (concretePeriodicSequence d m) n =
      (-1 : ℚ) ^ d * ((if m ∣ n + 2 * d then 1 else 0) - 1 / (m : ℚ)) := by
  simpa only [periodicCenteredMoment, pow_zero, mul_one] using
    concrete_periodic_boundary_sum d m n hd hm

end PartitionLaguerre

#print axioms PartitionLaguerre.critical_centered_transform_formula
#print axioms PartitionLaguerre.critical_centered_leading_eq
#print axioms PartitionLaguerre.critical_centered_degree_eq
#print axioms PartitionLaguerre.centered_cross_one_below
#print axioms PartitionLaguerre.centered_cross_two_below
#print axioms PartitionLaguerre.concrete_periodic_zeroth_moment
