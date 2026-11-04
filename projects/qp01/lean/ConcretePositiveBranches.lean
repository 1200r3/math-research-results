import ConcreteLeadingCoefficient

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem residue_coefficient_above_periodic (m j r h : ℕ) (F : ℕ → ℚ[X])
    (P : ℚ[X]) (b : ℕ → ℚ) (hF : ∀ s, F s = P + C (b s))
    (hh : P.natDegree < h) :
    (residueTransform m j F r).coeff h = (forwardSmoothPolynomial j P).coeff h := by
  have hc : (periodicCrossPolynomial m j P b r).coeff h = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((periodic_cross_degree_bound m j P b r).trans_lt hh)
  have hz : (C (periodicProductConstant m j b r)).coeff h = 0 :=
    Polynomial.coeff_C_of_ne_zero (by omega)
  rw [residue_transform_common_part m j r F P b hF, Polynomial.coeff_add,
    Polynomial.coeff_add, hc, hz, add_zero, add_zero]

theorem concrete_lower_order_leading_positive (d m j r : ℕ)
    (hd : 2 ≤ d) (hm : 2 ≤ m) (hj : j < d) :
    0 < (residueTransform m j (concreteResiduePolynomial d m) r).leadingCoeff := by
  let P := concretePolynomialPart d m
  have hP := concrete_polynomial_part_degree_leading d m (by omega) (by omega)
  have hs := forward_smooth_degree_leading j P (by rw [hP.1]; omega)
    (concrete_polynomial_part_nonzero d m (by omega) (by omega))
  have hsd : (forwardSmoothPolynomial j P).natDegree = 4 * d - 2 * j := by
    rw [hs.1, hP.1]
    omega
  have hpos : 0 < (forwardSmoothPolynomial j P).leadingCoeff := by
    rw [hs.2]
    apply mul_pos
    · exact mul_pos (sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
        (concrete_polynomial_part_nonzero d m (by omega) (by omega))))
        (by exact_mod_cast Nat.factorial_pos (2 * j))
    · exact_mod_cast Nat.choose_pos (show j ≤ P.natDegree by rw [hP.1]; omega)
  have hF (s : ℕ) : concreteResiduePolynomial d m s = P + C (concretePeriodicConstant d m s) :=
    concrete_residue_common_part d m s (by omega)
  have hc := residue_coefficient_above_periodic m j r (4 * d - 2 * j)
    (concreteResiduePolynomial d m) P (concretePeriodicConstant d m) hF
    (by rw [hP.1]; omega)
  have hsc : (forwardSmoothPolynomial j P).coeff (4 * d - 2 * j) =
      (forwardSmoothPolynomial j P).leadingCoeff := by
    rw [← hsd, Polynomial.coeff_natDegree]
  rw [hsc] at hc
  have hb := concrete_transform_degree_bound d m j r (by omega) (by omega) (by omega)
  have heq := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb (by rw [hc]; exact ne_of_gt hpos)
  rw [Polynomial.leadingCoeff, heq, hc]
  exact hpos

theorem concrete_boundary_rational_coefficient (d m r : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) =
      ((Nat.centralBinom d : ℚ) + 2 * (-1 : ℚ) ^ d *
        ((if m ∣ r + 2 * d then (m : ℚ) else 0) - 1)) /
          ((m : ℚ) ^ 2 * ((2 * d).factorial : ℚ)) := by
  rw [concrete_transform_boundary_coefficient d m r hd hm]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hfQ : ((2 * d).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * d)
  split_ifs <;> field_simp <;> ring

theorem concrete_noncritical_boundary_positive (d m r : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (ha : Even d ∨ (Odd d ∧ m < criticalIndex d)) :
    0 < (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) := by
  rw [concrete_boundary_rational_coefficient d m r (by omega) (by omega)]
  have hC : 2 < Nat.centralBinom d := by
    have h := Nat.centralBinom_strictMono (show 1 < d by omega)
    simpa only [show Nat.centralBinom 1 = 2 by rfl] using h
  have hCQ : 2 < (Nat.centralBinom d : ℚ) := by exact_mod_cast hC
  have hmQ : 2 ≤ (m : ℚ) := by exact_mod_cast hm
  have hnum : 0 < (Nat.centralBinom d : ℚ) + 2 * (-1 : ℚ) ^ d *
      ((if m ∣ r + 2 * d then (m : ℚ) else 0) - 1) := by
    rcases ha with he | ⟨ho, hbelow⟩
    · rw [he.neg_one_pow]
      split_ifs <;> linarith
    · rw [ho.neg_one_pow]
      have hnat : 2 * (m - 1) < Nat.centralBinom d := by
        unfold criticalIndex at hbelow
        omega
      have hcast : 2 * ((m : ℚ) - 1) < (Nat.centralBinom d : ℚ) := by
        have h : ((2 * (m - 1) : ℕ) : ℚ) < (Nat.centralBinom d : ℚ) := by exact_mod_cast hnat
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ m by omega),
          Nat.cast_one] using h
      split_ifs <;> linarith
  apply div_pos hnum
  have hf : 0 < ((2 * d).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos (2 * d)
  positivity

theorem concrete_noncritical_top_leading_positive (d m r : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (ha : Even d ∨ (Odd d ∧ m < criticalIndex d)) :
    0 < (residueTransform m d (concreteResiduePolynomial d m) r).leadingCoeff := by
  have hc := concrete_noncritical_boundary_positive d m r hd hm ha
  have hb := concrete_transform_degree_bound d m d r (by omega) (by omega) (le_refl d)
  have hb' : (residueTransform m d (concreteResiduePolynomial d m) r).natDegree ≤ 2 * d := by
    convert hb using 1 <;> omega
  have heq := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb' (ne_of_gt hc)
  rw [Polynomial.leadingCoeff, heq]
  exact hc

theorem eventual_positive_noncritical (d m : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (ha : Even d ∨ (Odd d ∧ m < criticalIndex d)) :
    eventualPositiveThrough d (partitionCount d m) := by
  apply eventual_positive_of_residue_model m d (by omega)
    (concreteResiduePolynomial d m) (partitionCount d m)
  · intro n
    exact concrete_partition_representation d m n (by omega)
  · intro j hj1 hjd r hr
    by_cases hj : j < d
    · exact concrete_lower_order_leading_positive d m j r hd hm hj
    · have heq : j = d := by omega
      subst j
      exact concrete_noncritical_top_leading_positive d m r hd hm ha

theorem main_classification_necessary (d m : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (hp : eventualPositiveThrough d (partitionCount d m)) :
    Even d ∨ (Odd d ∧ m ≤ criticalIndex d) := by
  by_contra hout
  obtain ⟨ho, habove⟩ := (outside_admissible_iff d m).mp hout
  exact eventual_positive_excludes_negative_class d m (partitionCount d m) (by omega)
    (by omega) (above_threshold_failure_proved d m hd hm ho habove) hp

/-- Precisely isolates the remaining odd equality branch. -/
theorem main_classification_of_odd_critical
    (hcritical : ∀ d : ℕ, 2 ≤ d → Odd d →
      eventualPositiveThrough d (partitionCount d (criticalIndex d))) : mainClassification := by
  apply main_classification_of_branches _ above_threshold_failure_proved
  intro d m hd hm ha
  rcases ha with he | ⟨ho, hle⟩
  · exact eventual_positive_noncritical d m hd hm (Or.inl he)
  · by_cases heq : m = criticalIndex d
    · subst m
      exact hcritical d hd ho
    · exact eventual_positive_noncritical d m hd hm (Or.inr ⟨ho, by omega⟩)

end PartitionLaguerre

#print axioms PartitionLaguerre.residue_coefficient_above_periodic
#print axioms PartitionLaguerre.concrete_lower_order_leading_positive
#print axioms PartitionLaguerre.concrete_boundary_rational_coefficient
#print axioms PartitionLaguerre.concrete_noncritical_boundary_positive
#print axioms PartitionLaguerre.concrete_noncritical_top_leading_positive
#print axioms PartitionLaguerre.eventual_positive_noncritical
#print axioms PartitionLaguerre.main_classification_necessary
#print axioms PartitionLaguerre.main_classification_of_odd_critical
