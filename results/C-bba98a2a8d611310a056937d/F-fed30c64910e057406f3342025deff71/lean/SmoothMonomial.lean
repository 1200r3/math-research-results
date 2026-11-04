import LaguerreMoments
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Expand

noncomputable section

namespace PartitionLaguerre

open Polynomial

def pairedShift (a b : ℕ) (c : ℚ) : ℚ[X] :=
  (X + C c) ^ a * (X - C c) ^ b

theorem paired_shift_degree (a b : ℕ) (c : ℚ) :
    (pairedShift a b c).natDegree = a + b := by
  unfold pairedShift
  rw [Polynomial.natDegree_mul (pow_ne_zero _ (monic_X_add_C c).ne_zero)
    (pow_ne_zero _ (monic_X_sub_C c).ne_zero),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow]
  simp

theorem reverse_power (P : ℚ[X]) (a : ℕ) :
    (P ^ a).reverse = P.reverse ^ a := by
  induction a with
  | zero =>
    simp only [pow_zero]
    exact Polynomial.reverse_C 1
  | succ a ih => rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]

theorem reverse_shift_linear (c : ℚ) :
    (X + C c).reverse = 1 + C c * X := by
  rw [Polynomial.reverse, Polynomial.natDegree_X_add_C, Polynomial.reflect_add,
    Polynomial.reflect_one_X, Polynomial.reflect_C, pow_one]

theorem paired_shift_reverse (a b : ℕ) (c : ℚ) :
    (pairedShift a b c).reverse =
      ((1 + X : ℚ[X]) ^ a * (1 - X : ℚ[X]) ^ b).comp (C c * X) := by
  have hneg : (X - C c : ℚ[X]) = X + C (-c) := by simp [sub_eq_add_neg]
  rw [pairedShift, Polynomial.reverse_mul_of_domain, reverse_power, reverse_power,
    hneg, reverse_shift_linear, reverse_shift_linear]
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp, map_neg]
  congr 2 <;> ring

/-- Homogeneity converts the high coefficient in X into a low coefficient
of a fixed polynomial in the shift. This avoids an unproved cancellation. -/
theorem paired_shift_coefficient (a b h : ℕ) (c : ℚ) (hh : h ≤ a + b) :
    (pairedShift a b c).coeff h =
      (((1 + X) ^ a * (1 - X) ^ b : ℚ[X]).coeff (a + b - h)) * c ^ (a + b - h) := by
  have heq := congrArg (fun P : ℚ[X] => P.coeff (a + b - h)) (paired_shift_reverse a b c)
  rw [Polynomial.coeff_reverse, paired_shift_degree,
    Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hh,
    Polynomial.comp_C_mul_X_coeff] at heq
  exact heq

def smoothMonomialPair (j a b : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (2 * j + 1),
    C (laguerreWeight j k) * pairedShift a b ((k : ℚ) - (j : ℚ))

theorem smooth_monomial_pair_coefficient (j a b h : ℕ) (hh : h ≤ a + b) :
    (smoothMonomialPair j a b).coeff h =
      (((1 + X) ^ a * (1 - X) ^ b : ℚ[X]).coeff (a + b - h)) *
        laguerreMoment j (a + b - h) := by
  simp only [smoothMonomialPair, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    paired_shift_coefficient a b h _ hh, laguerreMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem smooth_monomial_pair_degree_bound (j a b : ℕ) :
    (smoothMonomialPair j a b).natDegree ≤ a + b := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans (paired_shift_degree a b _).le

theorem smooth_monomial_pair_high_zero (j a b h : ℕ) (hh : a + b < h + 2 * j) :
    (smoothMonomialPair j a b).coeff h = 0 := by
  by_cases hbound : h ≤ a + b
  · rw [smooth_monomial_pair_coefficient j a b h hbound,
      laguerre_moment_below_order j (a + b - h) (by omega), mul_zero]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((smooth_monomial_pair_degree_bound j a b).trans_lt (by omega))

theorem one_sub_X_coefficient (q j : ℕ) :
    ((1 - X : ℚ[X]) ^ q).coeff j = (-1 : ℚ) ^ j * (q.choose j : ℚ) := by
  have heq : (1 - X : ℚ[X]) ^ q = ((1 + X) ^ q).comp (C (-1) * X) := by
    simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.one_comp,
      Polynomial.X_comp]
    congr 1
    simp [sub_eq_add_neg]
  rw [heq, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_one_add_X_pow, mul_comm]

theorem equal_power_pair_coefficient (q j : ℕ) :
    (((1 + X) ^ q * (1 - X) ^ q : ℚ[X]).coeff (2 * j)) =
      (-1 : ℚ) ^ j * (q.choose j : ℚ) := by
  have heq : ((1 + X) ^ q * (1 - X) ^ q : ℚ[X]) =
      Polynomial.expand ℚ 2 ((1 - X) ^ q) := by
    rw [Polynomial.expand_eq_comp_X_pow, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp, ← mul_pow]
    congr 1
    ring
  rw [heq, Polynomial.coeff_expand_mul' (by norm_num), one_sub_X_coefficient]

theorem smooth_monomial_pair_leading_coefficient (j q : ℕ) (hj : j ≤ q) :
    (smoothMonomialPair j q q).coeff (2 * q - 2 * j) =
      ((2 * j).factorial : ℚ) * (q.choose j : ℚ) := by
  have hh : 2 * q - 2 * j ≤ q + q := by omega
  have he : q + q - (2 * q - 2 * j) = 2 * j := by omega
  rw [smooth_monomial_pair_coefficient j q q (2 * q - 2 * j) hh, he,
    equal_power_pair_coefficient, laguerre_moment_at_order]
  have hs : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) *
        (((2 * j).factorial : ℚ) * (q.choose j : ℚ)) := by ring
    _ = _ := by rw [hs, one_mul]

end PartitionLaguerre

#print axioms PartitionLaguerre.paired_shift_degree
#print axioms PartitionLaguerre.reverse_power
#print axioms PartitionLaguerre.reverse_shift_linear
#print axioms PartitionLaguerre.paired_shift_reverse
#print axioms PartitionLaguerre.paired_shift_coefficient
#print axioms PartitionLaguerre.smooth_monomial_pair_coefficient
#print axioms PartitionLaguerre.smooth_monomial_pair_degree_bound
#print axioms PartitionLaguerre.smooth_monomial_pair_high_zero
#print axioms PartitionLaguerre.one_sub_X_coefficient
#print axioms PartitionLaguerre.equal_power_pair_coefficient
#print axioms PartitionLaguerre.smooth_monomial_pair_leading_coefficient
