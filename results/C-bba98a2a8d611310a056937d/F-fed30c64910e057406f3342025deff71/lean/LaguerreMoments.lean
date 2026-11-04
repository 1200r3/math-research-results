import PartitionDifference

noncomputable section

namespace PartitionLaguerre

open Polynomial

def laguerreWeight (j k : ℕ) : ℚ :=
  (-1 : ℚ) ^ (k + j) * ((2 * j).choose k : ℚ)

def laguerreMoment (j h : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * j + 1),
    laguerreWeight j k * ((k : ℚ) - (j : ℚ)) ^ h

theorem neg_one_pow_mod_two_congr (a b : ℕ) (hab : a % 2 = b % 2) :
    (-1 : ℚ) ^ a = (-1 : ℚ) ^ b := by
  calc
    _ = (-1 : ℚ) ^ (a % 2) := neg_one_pow_eq_pow_mod_two a
    _ = (-1 : ℚ) ^ (b % 2) := by rw [hab]
    _ = _ := (neg_one_pow_eq_pow_mod_two b).symm

theorem laguerre_weight_reflect (j k : ℕ) (hk : k ≤ 2 * j) :
    laguerreWeight j (2 * j - k) = laguerreWeight j k := by
  unfold laguerreWeight
  rw [Nat.choose_symm hk]
  congr 1
  exact neg_one_pow_mod_two_congr _ _ (by omega)

theorem laguerre_weighted_polynomial_sum (j : ℕ) (P : ℚ[X]) (x : ℚ) :
    (∑ k ∈ Finset.range (2 * j + 1), laguerreWeight j k * P.eval (x + (k : ℚ))) =
      (-1 : ℚ) ^ j * (((fwdDiff (1 : ℚ))^[2 * j]) P.eval x) := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * j := by have := Finset.mem_range.mp hk; omega
  have hsign : (-1 : ℚ) ^ (2 * j - k) = (-1 : ℚ) ^ k := by
    exact neg_one_pow_mod_two_congr _ _ (by omega)
  simp only [laguerreWeight, nsmul_eq_mul, mul_one, zsmul_eq_mul,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  rw [hsign, pow_add]
  ring

theorem laguerre_moment_below_order (j h : ℕ) (hh : h < 2 * j) :
    laguerreMoment j h = 0 := by
  have hw := laguerre_weighted_polynomial_sum j (X ^ h) (-(j : ℚ))
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hw
  have hz : ((fwdDiff (1 : ℚ))^[2 * j]) (fun x : ℚ => x ^ h) = 0 :=
    fwdDiff_iter_pow_eq_zero_of_lt hh
  have harg (k : ℕ) : -(j : ℚ) + (k : ℚ) = (k : ℚ) - (j : ℚ) := by ring
  simp only [harg, hz, Pi.zero_apply, mul_zero] at hw
  exact hw

theorem laguerre_moment_at_order (j : ℕ) :
    laguerreMoment j (2 * j) = (-1 : ℚ) ^ j * ((2 * j).factorial : ℚ) := by
  have hw := laguerre_weighted_polynomial_sum j (X ^ (2 * j)) (-(j : ℚ))
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hw
  have hf := fwdDiff_iter_eq_factorial (R := ℚ) (n := 2 * j)
  have harg (k : ℕ) : -(j : ℚ) + (k : ℚ) = (k : ℚ) - (j : ℚ) := by ring
  simpa only [laguerreMoment, harg, hf, Pi.natCast_apply] using hw

/-- Reflection gives every odd centered moment, not only those below 2j. -/
theorem laguerre_moment_odd (j h : ℕ) (hh : Odd h) :
    laguerreMoment j h = 0 := by
  have href : laguerreMoment j h = -laguerreMoment j h := by
    unfold laguerreMoment
    calc
      _ = ∑ k ∈ Finset.range (2 * j + 1),
          laguerreWeight j (2 * j + 1 - 1 - k) *
            (((2 * j + 1 - 1 - k : ℕ) : ℚ) - (j : ℚ)) ^ h :=
        (Finset.sum_range_reflect _ _).symm
      _ = ∑ k ∈ Finset.range (2 * j + 1),
          -(laguerreWeight j k * ((k : ℚ) - (j : ℚ)) ^ h) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ 2 * j := by have := Finset.mem_range.mp hk; omega
        have he : 2 * j + 1 - 1 - k = 2 * j - k := by omega
        have ha : ((2 * j - k : ℕ) : ℚ) - (j : ℚ) = -((k : ℚ) - (j : ℚ)) := by
          rw [Nat.cast_sub hk']
          push_cast
          ring
        rw [he, laguerre_weight_reflect j k hk', ha, neg_pow, hh.neg_one_pow]
        ring
      _ = _ := Finset.sum_neg_distrib _
  linarith

end PartitionLaguerre

#print axioms PartitionLaguerre.laguerre_weight_reflect
#print axioms PartitionLaguerre.neg_one_pow_mod_two_congr
#print axioms PartitionLaguerre.laguerre_weighted_polynomial_sum
#print axioms PartitionLaguerre.laguerre_moment_below_order
#print axioms PartitionLaguerre.laguerre_moment_at_order
#print axioms PartitionLaguerre.laguerre_moment_odd
