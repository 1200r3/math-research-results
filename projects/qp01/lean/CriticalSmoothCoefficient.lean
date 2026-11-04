import CriticalSmoothMonomials
import CriticalBinomialIdentities
import SmoothPolynomial

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem smooth_second_coefficient_reduction (d k : ℕ) (P : ℚ[X])
    (hP : P.natDegree = k + 2) (horder : 2 * d = k + 2) (hodd : P.coeff (k + 1) = 0) :
    (smoothPolynomialPair d P P).coeff k =
      P.leadingCoeff ^ 2 * (smoothMonomialPair d (k + 2) (k + 2)).coeff k +
      2 * P.leadingCoeff * P.coeff k * (smoothMonomialPair d (k + 2) k).coeff k := by
  let F := fun a b : ℕ => P.coeff a * P.coeff b * (smoothMonomialPair d a b).coeff k
  have htop : P.coeff (k + 2) = P.leadingCoeff := by rw [← hP, Polynomial.coeff_natDegree]
  have heq : (smoothPolynomialPair d P P).coeff k =
      ∑ a ∈ Finset.range (k + 3), ∑ b ∈ Finset.range (k + 3), F a b := by
    simp only [smoothPolynomialPair, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, hP, F]
  have hlowA (a b : ℕ) (ha : a < k) (hb : b ≤ k + 2) : F a b = 0 := by
    dsimp [F]
    rw [smooth_monomial_pair_high_zero d a b k (by omega), mul_zero]
  have hlowB (a b : ℕ) (ha : a ≤ k + 2) (hb : b < k) : F a b = 0 := by
    dsimp [F]
    rw [smooth_monomial_pair_high_zero d a b k (by omega), mul_zero]
  have hprefix : (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range (k + 3), F a b) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    exact hlowA a b (Finset.mem_range.mp ha) (by have := Finset.mem_range.mp hb; omega)
  have hrow (a : ℕ) (ha : a ≤ k + 2) :
      (∑ b ∈ Finset.range (k + 3), F a b) = F a k + F a (k + 1) + F a (k + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hz : (∑ b ∈ Finset.range k, F a b) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      exact hlowB a b ha (Finset.mem_range.mp hb)
    rw [hz, zero_add]
  rw [heq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    hprefix, zero_add, hrow k (by omega), hrow (k + 1) (by omega), hrow (k + 2) (by omega)]
  dsimp [F]
  simp only [hodd, zero_mul, mul_zero, zero_add, add_zero]
  have hkk : (smoothMonomialPair d k k).coeff k = 0 :=
    smooth_monomial_pair_high_zero d k k k (by omega)
  rw [hkk, smooth_monomial_pair_symm d k (k + 2), htop]
  ring

theorem centered_smooth_second_coefficient (d m : ℕ) (hd : 2 ≤ d) (hm : 0 < m) :
    (smoothPolynomialPair d (centeredPolynomialPart d m) (centeredPolynomialPart d m)).coeff (2 * d - 2) =
      (1 / ((m : ℚ) * ((2 * d).factorial : ℚ))) ^ 2 *
        ((2 * d).factorial : ℚ) * (Nat.centralBinom d : ℚ) * (d : ℚ) *
          ((m : ℚ) ^ 2 - 4 * (d : ℚ) ^ 2) / 12 := by
  let k := 2 * d - 2
  let P := centeredPolynomialPart d m
  have hP := centered_polynomial_degree_leading d m (by omega) hm
  have hidx : k + 2 = 2 * d := by dsimp [k]; omega
  have hodd : P.coeff (k + 1) = 0 := by
    apply centered_polynomial_odd_coefficient_zero d m (k + 1) (by omega) hm
    exact ⟨d - 1, by dsimp [k]; omega⟩
  have h := smooth_second_coefficient_reduction d k P (hP.1.trans hidx.symm) hidx.symm hodd
  rw [hidx] at h
  change (smoothPolynomialPair d P P).coeff (2 * d - 2) =
    P.leadingCoeff ^ 2 * (smoothMonomialPair d (2 * d) (2 * d)).coeff (2 * d - 2) +
      2 * P.leadingCoeff * P.coeff (2 * d - 2) *
        (smoothMonomialPair d (2 * d) (2 * d - 2)).coeff (2 * d - 2) at h
  rw [h, hP.2, centered_polynomial_second_coefficient d m hd hm,
    smooth_equal_critical_next_coefficient d (by omega), smooth_mixed_critical_coefficient d (by omega),
    critical_next_binomial, critical_binomial_difference d (by omega), critical_factorial_next_two]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hf : ((2 * d).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * d)
  have hd1 : (d + 1 : ℚ) ≠ 0 := by positivity
  have hden : 2 * (d : ℚ) - 1 ≠ 0 := by
    have h : 2 ≤ (d : ℚ) := by exact_mod_cast hd
    linarith
  have hden' : -1 + (d : ℚ) * 2 ≠ 0 := by
    have h : 2 ≤ (d : ℚ) := by exact_mod_cast hd
    linarith
  field_simp [hden, hden'] <;> ring_nf <;> field_simp [hden, hden'] <;> ring

end PartitionLaguerre

#print axioms PartitionLaguerre.smooth_second_coefficient_reduction
#print axioms PartitionLaguerre.centered_smooth_second_coefficient
