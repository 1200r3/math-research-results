import CriticalSmoothCoefficient
import CriticalBetaRational

noncomputable section

namespace PartitionLaguerre

open Polynomial

/-- The actual next coefficient, with all smooth and periodic terms linked. -/
theorem critical_centered_second_formula (d m r : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (ho : Odd d) (hr : m ∣ r + 2 * d) :
    (criticalCenteredTransform d m r).coeff (2 * d - 2) =
      betaExpressionQ d m (1 / ((m : ℚ) * ((2 * d).factorial : ℚ)))
        ((2 * d).factorial : ℚ) (Nat.centralBinom d) := by
  let P := centeredPolynomialPart d m
  let b := concretePeriodicConstant d m
  have hP := centered_polynomial_degree_leading d m (by omega) (by omega)
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hM0 : periodicCenteredMoment d 0 (fun n => b (n % m)) r = -((m : ℚ) - 1) / (m : ℚ) := by
    change periodicCenteredMoment d 0 (concretePeriodicSequence d m) r = _
    rw [concrete_periodic_zeroth_moment d m r (by omega) (by omega), if_pos hr, ho.neg_one_pow]
    field_simp <;> ring
  have hM2 : periodicCenteredMoment d 2 (fun n => b (n % m)) r =
      ((m : ℚ) - 1) / (m : ℚ) *
        (-(d : ℚ) ^ 2 + (d : ℚ) * (2 * (d : ℚ) - 1) * ((m : ℚ) + 1) / 6) :=
    concrete_exceptional_second_moment d m r hd hm ho hr
  have hdeg : P.natDegree = (2 * d - 2) + 2 := by rw [hP.1]; omega
  have hodd : P.coeff ((2 * d - 2) + 1) = 0 := by
    apply centered_polynomial_odd_coefficient_zero d m ((2 * d - 2) + 1) (by omega) (by omega)
    exact ⟨d - 1, by omega⟩
  have hc := centered_cross_two_below m d r (2 * d - 2) P b hdeg hodd
  rw [hM0, hM2, hP.2, centered_polynomial_second_coefficient d m hd (by omega)] at hc
  simp only [Nat.cast_sub (show 2 ≤ 2 * d by omega), Nat.cast_mul, Nat.cast_ofNat] at hc
  have hs := centered_smooth_second_coefficient d m hd (by omega)
  have hconst : (C (periodicProductConstant m d b r)).coeff (2 * d - 2) = 0 :=
    Polynomial.coeff_C_of_ne_zero (by omega)
  rw [critical_centered_transform_formula d m r (by omega), Polynomial.coeff_add,
    Polynomial.coeff_add, hs, hc, hconst, add_zero]
  dsimp [betaExpressionQ]
  ring

theorem critical_second_coefficient_eq_beta (d r : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hr : criticalIndex d ∣ r + 2 * d) :
    (criticalCenteredTransform d (criticalIndex d) r).coeff (2 * d - 2) = criticalBetaQ d := by
  exact critical_centered_second_formula d (criticalIndex d) r hd (critical_index_at_least_two d hd) ho hr

/-- Unconditional proof of the original full parameter classification. -/
theorem main_classification_proved : mainClassification := by
  apply main_classification_of_critical_second_positive
  intro d r hd ho hr hdiv
  rw [critical_second_coefficient_eq_beta d r hd ho hdiv]
  exact critical_beta_q_positive d hd ho

end PartitionLaguerre

#print axioms PartitionLaguerre.critical_centered_second_formula
#print axioms PartitionLaguerre.critical_second_coefficient_eq_beta
#check PartitionLaguerre.main_classification_proved
#print axioms PartitionLaguerre.main_classification_proved
