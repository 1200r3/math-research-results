import PolynomialPartDegree
import LaguerreMoments

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem iterated_difference_nat_restrict (f : ℚ → ℚ) (h n : ℕ) :
    ((fwdDiff (1 : ℕ))^[h]) (fun t => f (t : ℚ)) n =
      ((fwdDiff (1 : ℚ))^[h]) f (n : ℚ) := by
  induction h generalizing n with
  | zero => rfl
  | succ h ih =>
    simp only [Function.iterate_succ_apply', fwdDiff]
    rw [ih, ih]
    simp only [Nat.cast_add, Nat.cast_one]

theorem concrete_polynomial_full_difference (d m n : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    ((fwdDiff (1 : ℕ))^[2 * d]) (fun t => (concretePolynomialPart d m).eval (t : ℚ)) n =
      1 / (m : ℚ) := by
  have hP := concrete_polynomial_part_degree_leading d m hd hm
  rw [iterated_difference_nat_restrict (concretePolynomialPart d m).eval (2 * d) n, ← hP.1,
    (concretePolynomialPart d m).fwdDiff_iter_degree_eq_factorial]
  simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul, hP.1, hP.2]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hf : ((2 * d).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * d)
  field_simp

def concretePeriodicSequence (d m n : ℕ) : ℚ :=
  concretePeriodicConstant d m (n % m)

theorem concrete_periodic_sequence_period (d m n : ℕ) :
    concretePeriodicSequence d m (n + m) = concretePeriodicSequence d m n := by
  simp [concretePeriodicSequence]

/-- This is the actual periodic boundary term, derived by subtracting the
proved full differences of p and its common polynomial part. -/
theorem concrete_periodic_full_difference (d m n : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    ((fwdDiff (1 : ℕ))^[2 * d]) (concretePeriodicSequence d m) n =
      (if m ∣ n + 2 * d then 1 else 0) - 1 / (m : ℚ) := by
  have heq : partitionCount d m =
      (fun t : ℕ => (concretePolynomialPart d m).eval (t : ℚ)) + concretePeriodicSequence d m := by
    funext t
    exact partition_count_common_polynomial_part d m t hm
  have h := partition_count_iterated_difference d m n hd
  rw [heq, fwdDiff_iter_add, Pi.add_apply, concrete_polynomial_full_difference d m n hd hm] at h
  linarith

theorem laguerre_weighted_sequence_sum (j n : ℕ) (f : ℕ → ℚ) :
    (∑ k ∈ Finset.range (2 * j + 1), laguerreWeight j k * f (n + k)) =
      (-1 : ℚ) ^ j * (((fwdDiff (1 : ℕ))^[2 * j]) f n) := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * j := by have := Finset.mem_range.mp hk; omega
  have hsign : (-1 : ℚ) ^ (2 * j - k) = (-1 : ℚ) ^ k := by
    exact neg_one_pow_mod_two_congr _ _ (by omega)
  simp only [laguerreWeight, nsmul_eq_mul, mul_one, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_id]
  rw [hsign, pow_add]
  ring

theorem concrete_periodic_boundary_sum (d m n : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (∑ k ∈ Finset.range (2 * d + 1),
      laguerreWeight d k * concretePeriodicSequence d m (n + k)) =
      (-1 : ℚ) ^ d * ((if m ∣ n + 2 * d then 1 else 0) - 1 / (m : ℚ)) := by
  rw [laguerre_weighted_sequence_sum, concrete_periodic_full_difference d m n hd hm]

end PartitionLaguerre

#print axioms PartitionLaguerre.iterated_difference_nat_restrict
#print axioms PartitionLaguerre.concrete_polynomial_full_difference
#print axioms PartitionLaguerre.concrete_periodic_sequence_period
#print axioms PartitionLaguerre.concrete_periodic_full_difference
#print axioms PartitionLaguerre.laguerre_weighted_sequence_sum
#print axioms PartitionLaguerre.concrete_periodic_boundary_sum
