import ConcretePositiveBranches

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem critical_index_at_least_two (d : ℕ) (hd : 2 ≤ d) : 2 ≤ criticalIndex d := by
  have hC : 2 < Nat.centralBinom d := by
    have h := Nat.centralBinom_strictMono (show 1 < d by omega)
    simpa only [show Nat.centralBinom 1 = 2 by rfl] using h
  unfold criticalIndex
  omega

theorem concrete_odd_nonexceptional_leading_positive (d m r : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (ho : Odd d) (hr : ¬ m ∣ r + 2 * d) :
    0 < (residueTransform m d (concreteResiduePolynomial d m) r).leadingCoeff := by
  have heq : (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) =
      ((Nat.centralBinom d : ℚ) + 2) / ((m : ℚ) ^ 2 * ((2 * d).factorial : ℚ)) := by
    rw [concrete_boundary_rational_coefficient d m r (by omega) (by omega),
      if_neg hr, ho.neg_one_pow]
    ring
  have hc : 0 < (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) := by
    rw [heq]
    apply div_pos (by positivity)
    have hf : 0 < ((2 * d).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos (2 * d)
    positivity
  have hb := concrete_transform_degree_bound d m d r (by omega) (by omega) (le_refl d)
  have hb' : (residueTransform m d (concreteResiduePolynomial d m) r).natDegree ≤ 2 * d := by
    convert hb using 1 <;> omega
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb' (ne_of_gt hc)
  rw [Polynomial.leadingCoeff, hdeg]
  exact hc

theorem concrete_critical_boundary_zero (d r : ℕ) (hd : 2 ≤ d) (ho : Odd d)
    (hr : criticalIndex d ∣ r + 2 * d) :
    (residueTransform (criticalIndex d) d (concreteResiduePolynomial d (criticalIndex d)) r).coeff (2 * d) = 0 := by
  have hm := critical_index_at_least_two d hd
  have hdiv := Nat.two_dvd_centralBinom_of_one_le (show 0 < d by omega)
  have hmul := Nat.mul_div_cancel' hdiv
  have hCB : Nat.centralBinom d = 2 * (criticalIndex d - 1) := by
    unfold criticalIndex
    omega
  have hQ : (Nat.centralBinom d : ℚ) = 2 * ((criticalIndex d : ℚ) - 1) := by
    have h : (Nat.centralBinom d : ℚ) = ((2 * (criticalIndex d - 1) : ℕ) : ℚ) := by exact_mod_cast hCB
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ criticalIndex d by omega),
      Nat.cast_one] using h
  rw [concrete_boundary_rational_coefficient d (criticalIndex d) r (by omega) (by omega),
    if_pos hr, ho.neg_one_pow, hQ]
  ring

/-- All other residues and orders are already proved. This single remaining
sign obligation is on the actual exceptional critical residue polynomial. -/
theorem main_classification_of_critical_exceptional
    (hcritical : ∀ d : ℕ, 2 ≤ d → Odd d → ∀ r : ℕ, r < criticalIndex d →
      criticalIndex d ∣ r + 2 * d →
        0 < (residueTransform (criticalIndex d) d
          (concreteResiduePolynomial d (criticalIndex d)) r).leadingCoeff) : mainClassification := by
  apply main_classification_of_odd_critical
  intro d hd ho
  have hm := critical_index_at_least_two d hd
  apply eventual_positive_of_residue_model (criticalIndex d) d (by omega)
    (concreteResiduePolynomial d (criticalIndex d)) (partitionCount d (criticalIndex d))
  · intro n
    exact concrete_partition_representation d (criticalIndex d) n (by omega)
  · intro j hj1 hjd r hr
    by_cases hj : j < d
    · exact concrete_lower_order_leading_positive d (criticalIndex d) j r hd hm hj
    · have heq : j = d := by omega
      subst j
      by_cases hdiv : criticalIndex d ∣ r + 2 * d
      · exact hcritical d hd ho r hr hdiv
      · exact concrete_odd_nonexceptional_leading_positive d (criticalIndex d) r hd hm ho hdiv

end PartitionLaguerre

#print axioms PartitionLaguerre.critical_index_at_least_two
#print axioms PartitionLaguerre.concrete_odd_nonexceptional_leading_positive
#print axioms PartitionLaguerre.concrete_critical_boundary_zero
#print axioms PartitionLaguerre.main_classification_of_critical_exceptional
