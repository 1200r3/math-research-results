import CriticalCenteredTransform

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem polynomial_degree_drop (P : ℚ[X]) (N : ℕ) (hN : 0 < N)
    (hbound : P.natDegree ≤ N) (hzero : P.coeff N = 0) : P.natDegree < N := by
  by_contra hnot
  have heq : P.natDegree = N := by omega
  have hP : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [heq]; exact hN)
  apply Polynomial.leadingCoeff_ne_zero.mpr hP
  rw [Polynomial.leadingCoeff, heq, hzero]

theorem critical_centered_penultimate_zero (d m r : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (hr : m ∣ r + 2 * d) :
    (criticalCenteredTransform d m r).coeff (2 * d - 1) = 0 := by
  let P := centeredPolynomialPart d m
  let b := concretePeriodicConstant d m
  have hodd : Odd (2 * d - 1) := ⟨d - 1, by omega⟩
  have hpodd : P.coeff (2 * d - 1) = 0 :=
    centered_polynomial_odd_coefficient_zero d m (2 * d - 1) (by omega) (by omega) hodd
  have hsmooth : (smoothPolynomialPair d P P).coeff (2 * d - 1) = 0 :=
    smooth_polynomial_pair_odd_coefficient_zero d (2 * d - 1) P
      (centered_polynomial_even d m (by omega) (by omega)) hodd
  have hdeg : P.natDegree = (2 * d - 1) + 1 := by
    rw [(centered_polynomial_degree_leading d m (by omega) (by omega)).1]
    omega
  have hc := centered_cross_one_below m d r (2 * d - 1) P b hdeg hpodd
  have hM : periodicCenteredMoment d 1 (fun n => b (n % m)) r = 0 :=
    concrete_exceptional_first_moment d m r hd hm hr
  rw [hM, mul_zero] at hc
  have hconst : (C (periodicProductConstant m d b r)).coeff (2 * d - 1) = 0 :=
    Polynomial.coeff_C_of_ne_zero (by omega)
  rw [critical_centered_transform_formula d m r (by omega), Polynomial.coeff_add,
    Polynomial.coeff_add, hsmooth, hc, hconst]
  ring

theorem critical_centered_degree_bound (d r : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hr : criticalIndex d ∣ r + 2 * d) :
    (criticalCenteredTransform d (criticalIndex d) r).natDegree ≤ 2 * d - 2 := by
  have hm := critical_index_at_least_two d hd
  let P := residueTransform (criticalIndex d) d (concreteResiduePolynomial d (criticalIndex d)) r
  have hb : P.natDegree ≤ 2 * d := by
    have h := concrete_transform_degree_bound d (criticalIndex d) d r (by omega) (by omega) (le_refl d)
    convert h using 1 <;> omega
  have hz : P.coeff (2 * d) = 0 := concrete_critical_boundary_zero d r hd ho hr
  have hlt := polynomial_degree_drop P (2 * d) (by omega) hb hz
  have hcent : (criticalCenteredTransform d (criticalIndex d) r).natDegree < 2 * d := by
    rw [critical_centered_degree_eq]
    exact hlt
  have hsecond := polynomial_degree_drop (criticalCenteredTransform d (criticalIndex d) r)
    (2 * d - 1) (by omega) (by omega)
    (critical_centered_penultimate_zero d (criticalIndex d) r hd hm hr)
  omega

/-- The remaining obligation is precisely the actual q-2 coefficient. -/
theorem main_classification_of_critical_second_positive
    (hpositive : ∀ d r : ℕ, 2 ≤ d → Odd d → r < criticalIndex d →
      criticalIndex d ∣ r + 2 * d →
        0 < (criticalCenteredTransform d (criticalIndex d) r).coeff (2 * d - 2)) :
    mainClassification := by
  apply main_classification_of_critical_exceptional
  intro d hd ho r hr hdiv
  have hc := hpositive d r hd ho hr hdiv
  have hb := critical_centered_degree_bound d r hd ho hdiv
  have heq := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb (ne_of_gt hc)
  rw [← critical_centered_leading_eq d (criticalIndex d) r, Polynomial.leadingCoeff, heq]
  exact hc

end PartitionLaguerre

#print axioms PartitionLaguerre.polynomial_degree_drop
#print axioms PartitionLaguerre.critical_centered_penultimate_zero
#print axioms PartitionLaguerre.critical_centered_degree_bound
#print axioms PartitionLaguerre.main_classification_of_critical_second_positive
