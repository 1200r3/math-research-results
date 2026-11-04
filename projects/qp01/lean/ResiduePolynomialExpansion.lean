import SmoothPolynomial
import PeriodicDifference

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem polynomial_shift_degree_leading (P : ℚ[X]) (c : ℚ) :
    (P.comp (X + C c)).natDegree = P.natDegree ∧
      (P.comp (X + C c)).leadingCoeff = P.leadingCoeff := by
  constructor
  · simp [Polynomial.natDegree_comp]
  · rw [Polynomial.leadingCoeff_comp (by simp), Polynomial.leadingCoeff_X_add_C,
      one_pow, mul_one]

def forwardSmoothPolynomial (j : ℕ) (P : ℚ[X]) : ℚ[X] :=
  (smoothPolynomialPair j P P).comp (X + C (j : ℚ))

theorem forward_smooth_polynomial_formula (j : ℕ) (P : ℚ[X]) :
    forwardSmoothPolynomial j P =
      ∑ k ∈ Finset.range (2 * j + 1),
        C (laguerreWeight j k) * P.comp (X + C (k : ℚ)) *
          P.comp (X + C ((2 * j - k : ℕ) : ℚ)) := by
  unfold forwardSmoothPolynomial
  rw [smooth_polynomial_pair_formula, Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * j := by have := Finset.mem_range.mp hk; omega
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc,
    Polynomial.add_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hplus : X + C (j : ℚ) + C ((k : ℚ) - (j : ℚ)) = (X + C (k : ℚ) : ℚ[X]) := by
    simp only [map_sub]
    ring
  have hminus : X + C (j : ℚ) - C ((k : ℚ) - (j : ℚ)) =
      (X + C ((2 * j - k : ℕ) : ℚ) : ℚ[X]) := by
    rw [Nat.cast_sub hk']
    push_cast
    simp only [map_sub, map_mul, map_ofNat]
    ring
  rw [hplus, hminus]

def periodicCrossPolynomial (m j : ℕ) (P : ℚ[X]) (b : ℕ → ℚ) (r : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (2 * j + 1), C (laguerreWeight j k) *
    (C (b ((r + k) % m)) * P.comp (X + C ((2 * j - k : ℕ) : ℚ)) +
      C (b ((r + (2 * j - k)) % m)) * P.comp (X + C (k : ℚ)))

def periodicProductConstant (m j : ℕ) (b : ℕ → ℚ) (r : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * j + 1),
    laguerreWeight j k * b ((r + k) % m) * b ((r + (2 * j - k)) % m)

theorem periodic_cross_degree_bound (m j : ℕ) (P : ℚ[X]) (b : ℕ → ℚ) (r : ℕ) :
    (periodicCrossPolynomial m j P b r).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (polynomial_shift_degree_leading P _).1.le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (polynomial_shift_degree_leading P _).1.le

theorem reflected_periodic_weight_sum (m j r : ℕ) (b : ℕ → ℚ) :
    (∑ k ∈ Finset.range (2 * j + 1),
      laguerreWeight j k * b ((r + (2 * j - k)) % m)) =
    ∑ k ∈ Finset.range (2 * j + 1), laguerreWeight j k * b ((r + k) % m) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ 2 * j := by have := Finset.mem_range.mp hk; omega
  have he : 2 * j + 1 - 1 - k = 2 * j - k := by omega
  rw [he, laguerre_weight_reflect j k hk', Nat.sub_sub_self hk']

theorem periodic_cross_top_coefficient (m j : ℕ) (P : ℚ[X]) (b : ℕ → ℚ) (r : ℕ) :
    (periodicCrossPolynomial m j P b r).coeff P.natDegree =
      2 * P.leadingCoeff *
        ∑ k ∈ Finset.range (2 * j + 1), laguerreWeight j k * b ((r + k) % m) := by
  have hcoeff (c : ℚ) : (P.comp (X + C c)).coeff P.natDegree = P.leadingCoeff := by
    rw [← (polynomial_shift_degree_leading P c).1, Polynomial.coeff_natDegree,
      (polynomial_shift_degree_leading P c).2]
  simp only [periodicCrossPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_add, hcoeff]
  calc
    _ = P.leadingCoeff *
        (∑ k ∈ Finset.range (2 * j + 1), laguerreWeight j k * b ((r + k) % m)) +
      P.leadingCoeff * (∑ k ∈ Finset.range (2 * j + 1),
        laguerreWeight j k * b ((r + (2 * j - k)) % m)) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [reflected_periodic_weight_sum]; ring

theorem residue_transform_common_part (m j r : ℕ) (F : ℕ → ℚ[X])
    (P : ℚ[X]) (b : ℕ → ℚ) (hF : ∀ s, F s = P + C (b s)) :
    residueTransform m j F r = forwardSmoothPolynomial j P +
      periodicCrossPolynomial m j P b r + C (periodicProductConstant m j b r) := by
  rw [forward_smooth_polynomial_formula]
  unfold residueTransform periodicCrossPolynomial periodicProductConstant
  simp only [hF, Polynomial.add_comp, Polynomial.C_comp, map_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [laguerreWeight, map_mul]
  ring

end PartitionLaguerre

#print axioms PartitionLaguerre.polynomial_shift_degree_leading
#print axioms PartitionLaguerre.forward_smooth_polynomial_formula
#print axioms PartitionLaguerre.periodic_cross_degree_bound
#print axioms PartitionLaguerre.reflected_periodic_weight_sum
#print axioms PartitionLaguerre.periodic_cross_top_coefficient
#print axioms PartitionLaguerre.residue_transform_common_part
