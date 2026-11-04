import ResiduePolynomialExpansion
import MainReduction

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem forward_smooth_degree_leading (j : ℕ) (P : ℚ[X])
    (hj : j ≤ P.natDegree) (hP : P ≠ 0) :
    (forwardSmoothPolynomial j P).natDegree = 2 * P.natDegree - 2 * j ∧
      (forwardSmoothPolynomial j P).leadingCoeff =
        P.leadingCoeff ^ 2 * ((2 * j).factorial : ℚ) * (P.natDegree.choose j : ℚ) := by
  have hs := smooth_polynomial_pair_degree_leading j P hj hP
  have ht := polynomial_shift_degree_leading (smoothPolynomialPair j P P) (j : ℚ)
  exact ⟨ht.1.trans hs.1, ht.2.trans hs.2⟩

theorem residue_common_part_degree_bound (m j r : ℕ) (F : ℕ → ℚ[X])
    (P : ℚ[X]) (b : ℕ → ℚ) (hF : ∀ s, F s = P + C (b s))
    (hj : 2 * j ≤ P.natDegree) (hP : P ≠ 0) :
    (residueTransform m j F r).natDegree ≤ 2 * P.natDegree - 2 * j := by
  rw [residue_transform_common_part m j r F P b hF, Polynomial.natDegree_add_C]
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (forward_smooth_degree_leading j P (by omega) hP).1.le
  · exact (periodic_cross_degree_bound m j P b r).trans (by omega)

theorem concrete_polynomial_part_nonzero (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    concretePolynomialPart d m ≠ 0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  rw [(concrete_polynomial_part_degree_leading d m hd hm).2]
  have hf : 0 < ((2 * d).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos (2 * d)
  positivity

theorem concrete_transform_degree_bound (d m j r : ℕ) (hd : 1 ≤ d) (hm : 0 < m)
    (hj : j ≤ d) :
    (residueTransform m j (concreteResiduePolynomial d m) r).natDegree ≤ 4 * d - 2 * j := by
  have hF (s : ℕ) : concreteResiduePolynomial d m s =
      concretePolynomialPart d m + C (concretePeriodicConstant d m s) :=
    concrete_residue_common_part d m s hm
  have h := residue_common_part_degree_bound m j r (concreteResiduePolynomial d m)
    (concretePolynomialPart d m) (concretePeriodicConstant d m) hF
    (by rw [(concrete_polynomial_part_degree_leading d m hd hm).1]; omega)
    (concrete_polynomial_part_nonzero d m hd hm)
  rw [(concrete_polynomial_part_degree_leading d m hd hm).1] at h
  convert h using 1 <;> omega

/-- The actual coefficient of the critical-order transform, before deciding
whether it vanishes. This is not a leading-coefficient claim at equality. -/
theorem concrete_transform_boundary_coefficient (d m r : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) =
      (1 / ((m : ℚ) * ((2 * d).factorial : ℚ))) ^ 2 *
        ((2 * d).factorial : ℚ) * (Nat.centralBinom d : ℚ) +
      2 * (1 / ((m : ℚ) * ((2 * d).factorial : ℚ))) * (-1 : ℚ) ^ d *
        ((if m ∣ r + 2 * d then 1 else 0) - 1 / (m : ℚ)) := by
  let P := concretePolynomialPart d m
  let b := concretePeriodicConstant d m
  have hP := concrete_polynomial_part_degree_leading d m hd hm
  have hF (s : ℕ) : concreteResiduePolynomial d m s = P + C (b s) :=
    concrete_residue_common_part d m s hm
  have hs := forward_smooth_degree_leading d P (by rw [hP.1]; omega)
    (concrete_polynomial_part_nonzero d m hd hm)
  have hsd : (forwardSmoothPolynomial d P).natDegree = 2 * d := by
    rw [hs.1, hP.1]
    omega
  have hsc : (forwardSmoothPolynomial d P).coeff (2 * d) =
      (1 / ((m : ℚ) * ((2 * d).factorial : ℚ))) ^ 2 *
        ((2 * d).factorial : ℚ) * (Nat.centralBinom d : ℚ) := by
    calc
      _ = (forwardSmoothPolynomial d P).leadingCoeff := by
        rw [← hsd, Polynomial.coeff_natDegree]
      _ = _ := by
        rw [hs.2, hP.1, hP.2, Nat.centralBinom_eq_two_mul_choose]
  have hc := periodic_cross_top_coefficient m d P b r
  rw [hP.1, hP.2] at hc
  have hb := concrete_periodic_boundary_sum d m r hd hm
  change (∑ k ∈ Finset.range (2 * d + 1), laguerreWeight d k * b ((r + k) % m)) = _ at hb
  rw [hb] at hc
  have hz : (C (periodicProductConstant m d b r)).coeff (2 * d) = 0 := by
    exact Polynomial.coeff_C_of_ne_zero (by omega)
  rw [residue_transform_common_part m d r (concreteResiduePolynomial d m) P b hF,
    Polynomial.coeff_add, Polynomial.coeff_add, hsc, hc, hz, add_zero]
  ring

theorem concrete_above_threshold_coefficient_negative (d m r : ℕ)
    (hd : 2 ≤ d) (hm : 2 ≤ m) (ho : Odd d) (habove : criticalIndex d < m)
    (hr : m ∣ r + 2 * d) :
    (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) < 0 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hfQ : ((2 * d).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * d)
  have hnat : Nat.centralBinom d < 2 * (m - 1) := by
    unfold criticalIndex at habove
    omega
  have hcast : (Nat.centralBinom d : ℚ) < 2 * ((m : ℚ) - 1) := by
    have h : (Nat.centralBinom d : ℚ) < ((2 * (m - 1) : ℕ) : ℚ) := by exact_mod_cast hnat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (show 1 ≤ m by omega),
      Nat.cast_one] using h
  have heq :
      (residueTransform m d (concreteResiduePolynomial d m) r).coeff (2 * d) =
        ((Nat.centralBinom d : ℚ) - 2 * ((m : ℚ) - 1)) /
          ((m : ℚ) ^ 2 * ((2 * d).factorial : ℚ)) := by
    rw [concrete_transform_boundary_coefficient d m r (by omega) (by omega),
      if_pos hr, ho.neg_one_pow]
    field_simp
    ring
  rw [heq]
  apply div_neg_of_neg_of_pos (sub_neg.mpr hcast)
  have hf : 0 < ((2 * d).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos (2 * d)
  positivity

theorem concrete_above_threshold_leading_negative (d m r : ℕ)
    (hd : 2 ≤ d) (hm : 2 ≤ m) (ho : Odd d) (habove : criticalIndex d < m)
    (hr : m ∣ r + 2 * d) :
    (residueTransform m d (concreteResiduePolynomial d m) r).leadingCoeff < 0 := by
  have hc := concrete_above_threshold_coefficient_negative d m r hd hm ho habove hr
  have hb := concrete_transform_degree_bound d m d r (by omega) (by omega) (le_refl d)
  have hb' : (residueTransform m d (concreteResiduePolynomial d m) r).natDegree ≤ 2 * d := by
    convert hb using 1 <;> omega
  have heq := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb' (ne_of_lt hc)
  rw [Polynomial.leadingCoeff, heq]
  exact hc

/-- Unconditional proof of the original above-threshold Prop. -/
theorem above_threshold_failure_proved : aboveThresholdFailure := by
  intro d m hd hm ho habove
  apply eventual_negative_of_residue_model m d (by omega) (by omega)
    (concreteResiduePolynomial d m) (partitionCount d m)
  · intro n
    exact concrete_partition_representation d m n (by omega)
  · intro r hr hdiv
    exact concrete_above_threshold_leading_negative d m r hd hm ho habove hdiv

end PartitionLaguerre

#print axioms PartitionLaguerre.forward_smooth_degree_leading
#print axioms PartitionLaguerre.residue_common_part_degree_bound
#print axioms PartitionLaguerre.concrete_polynomial_part_nonzero
#print axioms PartitionLaguerre.concrete_transform_degree_bound
#print axioms PartitionLaguerre.concrete_transform_boundary_coefficient
#print axioms PartitionLaguerre.concrete_above_threshold_coefficient_negative
#print axioms PartitionLaguerre.concrete_above_threshold_leading_negative
#check PartitionLaguerre.above_threshold_failure_proved
#print axioms PartitionLaguerre.above_threshold_failure_proved
