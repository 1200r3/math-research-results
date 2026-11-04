import NextLaguerreMoment
import SmoothMonomial

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem smooth_monomial_pair_symm (j a b : ℕ) :
    smoothMonomialPair j a b = smoothMonomialPair j b a := by
  unfold smoothMonomialPair
  conv_lhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * j := by have := Finset.mem_range.mp hk; omega
  have he : 2 * j + 1 - 1 - k = 2 * j - k := by omega
  have ha : ((2 * j - k : ℕ) : ℚ) - (j : ℚ) = -((k : ℚ) - (j : ℚ)) := by
    rw [Nat.cast_sub hk']
    push_cast
    ring
  rw [he, laguerre_weight_reflect j k hk', ha]
  have hp (u : ℚ) : pairedShift a b (-u) = pairedShift b a u := by
    simp only [pairedShift, map_neg, sub_neg_eq_add]
    rw [show (X + -C u : ℚ[X]) = X - C u by ring]
    exact mul_comm _ _
  rw [hp]

theorem mixed_power_pair_coefficient (d : ℕ) (hd : 1 ≤ d) :
    (((1 + X) ^ (2 * d) * (1 - X) ^ (2 * d - 2) : ℚ[X]).coeff (2 * d)) =
      (-1 : ℚ) ^ d *
        ((((2 * d - 2).choose d : ℕ) : ℚ) - (((2 * d - 2).choose (d - 1) : ℕ) : ℚ)) := by
  let n := 2 * d - 2
  let R : ℚ[X] := Polynomial.expand ℚ 2 ((1 - X) ^ n)
  have hR : ((1 + X) ^ n * (1 - X) ^ n : ℚ[X]) = R := by
    rw [← mul_pow]
    dsimp [R]
    rw [Polynomial.expand_eq_comp_X_pow, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp]
    congr 1
    ring
  have hQ : ((1 + X) ^ (2 * d) * (1 - X) ^ n : ℚ[X]) =
      R + C 2 * (R * X) + R * X ^ 2 := by
    rw [show 2 * d = n + 2 by dsimp [n]; omega, pow_add]
    calc
      _ = ((1 + X) ^ n * (1 - X) ^ n) * (1 + X) ^ 2 := by ring
      _ = R * (1 + X) ^ 2 := by rw [hR]
      _ = _ := by
        rw [show (C (2 : ℚ) : ℚ[X]) = 2 from Polynomial.C_eq_natCast 2]
        ring
  have hhigh : R.coeff (2 * d) = (-1 : ℚ) ^ d * (n.choose d : ℚ) := by
    dsimp [R]
    rw [Polynomial.coeff_expand_mul' (by norm_num), one_sub_X_coefficient]
  have hlow : R.coeff (2 * d - 2) = (-1 : ℚ) ^ (d - 1) * (n.choose (d - 1) : ℚ) := by
    dsimp [R]
    rw [show 2 * d - 2 = 2 * (d - 1) by omega,
      Polynomial.coeff_expand_mul' (by norm_num), one_sub_X_coefficient]
  have hodd : R.coeff (2 * d - 1) = 0 := by
    dsimp [R]
    have hn : ¬ 2 ∣ 2 * d - 1 := by
      intro h
      have hmod := Nat.mod_eq_zero_of_dvd h
      omega
    simp only [Polynomial.coeff_expand (p := 2) (by norm_num), if_neg hn]
  have hx1 : (R * X).coeff (2 * d) = R.coeff (2 * d - 1) := by
    simpa only [show 2 * d - 1 + 1 = 2 * d by omega] using Polynomial.coeff_mul_X R (2 * d - 1)
  have hx2 : (R * X ^ 2).coeff (2 * d) = R.coeff (2 * d - 2) := by
    simpa only [show 2 * d - 2 + 2 = 2 * d by omega] using Polynomial.coeff_mul_X_pow R 2 (2 * d - 2)
  have hsign : (-1 : ℚ) ^ (d - 1) = -(-1 : ℚ) ^ d := by
    calc
      _ = -((-1 : ℚ) ^ (d - 1) * (-1)) := by ring
      _ = _ := by rw [← pow_succ, show d - 1 + 1 = d by omega]
  rw [hQ, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    hx1, hx2, hhigh, hlow, hodd, hsign]
  ring

theorem smooth_mixed_critical_coefficient (d : ℕ) (hd : 1 ≤ d) :
    (smoothMonomialPair d (2 * d) (2 * d - 2)).coeff (2 * d - 2) =
      ((2 * d).factorial : ℚ) *
        ((((2 * d - 2).choose d : ℕ) : ℚ) - (((2 * d - 2).choose (d - 1) : ℕ) : ℚ)) := by
  rw [smooth_monomial_pair_coefficient d (2 * d) (2 * d - 2) (2 * d - 2) (by omega),
    show 2 * d + (2 * d - 2) - (2 * d - 2) = 2 * d by omega,
    mixed_power_pair_coefficient d hd, laguerre_moment_at_order]
  have hs : (-1 : ℚ) ^ d * (-1 : ℚ) ^ d = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℚ) ^ d * (-1 : ℚ) ^ d) * (((2 * d).factorial : ℚ) *
      ((((2 * d - 2).choose d : ℕ) : ℚ) - (((2 * d - 2).choose (d - 1) : ℕ) : ℚ))) := by ring
    _ = _ := by rw [hs, one_mul]

theorem smooth_equal_critical_next_coefficient (d : ℕ) (hd : 1 ≤ d) :
    (smoothMonomialPair d (2 * d) (2 * d)).coeff (2 * d - 2) =
      -(((2 * d).choose (d + 1) : ℕ) : ℚ) * ((2 * d + 2).factorial : ℚ) * (d : ℚ) / 12 := by
  rw [smooth_monomial_pair_coefficient d (2 * d) (2 * d) (2 * d - 2) (by omega),
    show 2 * d + 2 * d - (2 * d - 2) = 2 * d + 2 by omega]
  have hcoeff : (((1 + X) ^ (2 * d) * (1 - X) ^ (2 * d) : ℚ[X]).coeff (2 * d + 2)) =
      (-1 : ℚ) ^ (d + 1) * (((2 * d).choose (d + 1) : ℕ) : ℚ) := by
    convert equal_power_pair_coefficient (2 * d) (d + 1) using 1 <;> congr 1 <;> omega
  rw [hcoeff, laguerre_moment_next_even d hd]
  have hs : (-1 : ℚ) ^ (d + 1) * (-1 : ℚ) ^ d = -1 := by
    rw [← pow_add]
    exact (show Odd (d + 1 + d) from ⟨d, by omega⟩).neg_one_pow
  calc
    _ = ((-1 : ℚ) ^ (d + 1) * (-1 : ℚ) ^ d) *
      ((((2 * d).choose (d + 1) : ℕ) : ℚ) * ((2 * d + 2).factorial : ℚ) * (d : ℚ) / 12) := by ring
    _ = _ := by rw [hs]; ring

end PartitionLaguerre

#print axioms PartitionLaguerre.smooth_monomial_pair_symm
#print axioms PartitionLaguerre.mixed_power_pair_coefficient
#print axioms PartitionLaguerre.smooth_mixed_critical_coefficient
#print axioms PartitionLaguerre.smooth_equal_critical_next_coefficient
