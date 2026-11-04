import SmoothMonomial

noncomputable section

namespace PartitionLaguerre

open Polynomial

def smoothPolynomialPair (j : ℕ) (P Q : ℚ[X]) : ℚ[X] :=
  ∑ a ∈ Finset.range (P.natDegree + 1),
    ∑ b ∈ Finset.range (Q.natDegree + 1),
      C (P.coeff a * Q.coeff b) * smoothMonomialPair j a b

theorem smooth_polynomial_pair_formula (j : ℕ) (P Q : ℚ[X]) :
    smoothPolynomialPair j P Q =
      ∑ k ∈ Finset.range (2 * j + 1),
        C (laguerreWeight j k) * P.comp (X + C ((k : ℚ) - (j : ℚ))) *
          Q.comp (X - C ((k : ℚ) - (j : ℚ))) := by
  let T := fun k a b : ℕ => C (laguerreWeight j k) *
    (C (P.coeff a) * (X + C ((k : ℚ) - (j : ℚ))) ^ a) *
    (C (Q.coeff b) * (X - C ((k : ℚ) - (j : ℚ))) ^ b)
  have hP (S : ℚ[X]) : P.comp S =
      ∑ a ∈ Finset.range (P.natDegree + 1), C (P.coeff a) * S ^ a :=
    Polynomial.eval₂_eq_sum_range Polynomial.C S
  have hQ (S : ℚ[X]) : Q.comp S =
      ∑ b ∈ Finset.range (Q.natDegree + 1), C (Q.coeff b) * S ^ b :=
    Polynomial.eval₂_eq_sum_range Polynomial.C S
  calc
    _ = ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          ∑ k ∈ Finset.range (2 * j + 1), T k a b := by
      simp only [smoothPolynomialPair, smoothMonomialPair, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [T, pairedShift]
      rw [map_mul]
      ring
    _ = ∑ k ∈ Finset.range (2 * j + 1),
        ∑ a ∈ Finset.range (P.natDegree + 1),
          ∑ b ∈ Finset.range (Q.natDegree + 1), T k a b := by
      simp_rw [Finset.sum_comm (s := Finset.range (Q.natDegree + 1))
        (t := Finset.range (2 * j + 1))]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hP, hQ]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

theorem smooth_polynomial_pair_high_zero (j h : ℕ) (P : ℚ[X])
    (hh : 2 * P.natDegree < h + 2 * j) :
    (smoothPolynomialPair j P P).coeff h = 0 := by
  simp only [smoothPolynomialPair, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  rw [smooth_monomial_pair_high_zero j a b h (by omega), mul_zero]

theorem smooth_polynomial_pair_top_coefficient (j : ℕ) (P : ℚ[X])
    (hj : j ≤ P.natDegree) :
    (smoothPolynomialPair j P P).coeff (2 * P.natDegree - 2 * j) =
      P.leadingCoeff ^ 2 * ((2 * j).factorial : ℚ) * (P.natDegree.choose j : ℚ) := by
  let D := P.natDegree
  let U : ℚ := P.coeff D * P.coeff D *
    (((2 * j).factorial : ℚ) * (D.choose j : ℚ))
  have he : 2 * D - 2 * j + 2 * j = 2 * D := Nat.sub_add_cancel (Nat.mul_le_mul_left 2 hj)
  calc
    _ = ∑ a ∈ Finset.range (D + 1), ∑ b ∈ Finset.range (D + 1),
        (if a = D ∧ b = D then U else 0) := by
      simp only [smoothPolynomialPair, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      by_cases hab : a = D ∧ b = D
      · rcases hab with ⟨rfl, rfl⟩
        rw [smooth_monomial_pair_leading_coefficient j D hj, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg hab, smooth_monomial_pair_high_zero j a b
          (2 * D - 2 * j) (by omega), mul_zero]
    _ = U := by
      rw [Finset.sum_eq_single D]
      · rw [Finset.sum_eq_single D]
        · simp
        · intro b hb hne
          simp [hne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self D)))
      · intro a ha hne
        apply Finset.sum_eq_zero
        intro b hb
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self D)))
    _ = _ := by
      change P.leadingCoeff * P.leadingCoeff *
        (((2 * j).factorial : ℚ) * (P.natDegree.choose j : ℚ)) = _
      ring

theorem smooth_polynomial_pair_degree_leading (j : ℕ) (P : ℚ[X])
    (hj : j ≤ P.natDegree) (hP : P ≠ 0) :
    (smoothPolynomialPair j P P).natDegree = 2 * P.natDegree - 2 * j ∧
      (smoothPolynomialPair j P P).leadingCoeff =
        P.leadingCoeff ^ 2 * ((2 * j).factorial : ℚ) * (P.natDegree.choose j : ℚ) := by
  have hc := smooth_polynomial_pair_top_coefficient j P hj
  have hpos : 0 < P.leadingCoeff ^ 2 * ((2 * j).factorial : ℚ) * (P.natDegree.choose j : ℚ) := by
    apply mul_pos
    · exact mul_pos (sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP))
        (by exact_mod_cast Nat.factorial_pos (2 * j))
    · exact_mod_cast Nat.choose_pos hj
  have hb : (smoothPolynomialPair j P P).natDegree ≤ 2 * P.natDegree - 2 * j := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro h hh
    exact smooth_polynomial_pair_high_zero j h P (by omega)
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb (by rw [hc]; exact ne_of_gt hpos)
  exact ⟨hd, by rw [Polynomial.leadingCoeff, hd, hc]⟩

end PartitionLaguerre

#print axioms PartitionLaguerre.smooth_polynomial_pair_formula
#print axioms PartitionLaguerre.smooth_polynomial_pair_high_zero
#print axioms PartitionLaguerre.smooth_polynomial_pair_top_coefficient
#print axioms PartitionLaguerre.smooth_polynomial_pair_degree_leading
