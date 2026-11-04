import PolynomialPart

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem bernoulli_polynomial_degree_leading (n : ℕ) :
    (Polynomial.bernoulli n).natDegree = n ∧
      (Polynomial.bernoulli n).leadingCoeff = 1 := by
  have ht : (Polynomial.bernoulli n).coeff n = 1 := by
    simp [Polynomial.coeff_bernoulli]
  have hb : (Polynomial.bernoulli n).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    simp [Polynomial.coeff_bernoulli, Nat.not_le.mpr hi]
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hb (by rw [ht]; norm_num)
  exact ⟨hd, by rw [Polynomial.leadingCoeff, hd, ht]⟩

theorem inclusive_power_sum_degree_leading (k : ℕ) :
    (inclusivePowerSum k).natDegree = k + 1 ∧
      (inclusivePowerSum k).leadingCoeff = (k + 1 : ℚ)⁻¹ := by
  have hb := bernoulli_polynomial_degree_leading (k + 1)
  have ha : (k + 1 : ℚ) ≠ 0 := by positivity
  have hq : ((Polynomial.bernoulli (k + 1)).comp (X + 1)).natDegree = k + 1 := by
    simp [Polynomial.natDegree_comp, hb.1]
  have hlt : (C (_root_.bernoulli (k + 1))).degree <
      ((Polynomial.bernoulli (k + 1)).comp (X + 1)).degree := by
    apply Polynomial.degree_lt_degree
    simp only [Polynomial.natDegree_C, hq]
    omega
  constructor
  · simp [inclusivePowerSum, Polynomial.natDegree_C_mul (inv_ne_zero ha),
      Polynomial.natDegree_sub_C, hq]
  · rw [inclusivePowerSum, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_sub_of_degree_lt hlt,
      Polynomial.leadingCoeff_comp (by simp), hb.2]
    have hlin : (X + 1 : ℚ[X]).leadingCoeff = 1 := Polynomial.leadingCoeff_X_add_C 1
    simp only [hlin, one_pow, mul_one]

theorem inclusive_polynomial_sum_degree_leading (P : ℚ[X]) (hP : P ≠ 0) :
    (inclusivePolynomialSum P).natDegree = P.natDegree + 1 ∧
      (inclusivePolynomialSum P).leadingCoeff = P.leadingCoeff / (P.natDegree + 1 : ℚ) := by
  let D := P.natDegree
  let L : ℚ[X] := ∑ i ∈ Finset.range D, C (P.coeff i) * inclusivePowerSum i
  let H : ℚ[X] := C (P.coeff D) * inclusivePowerSum D
  have htop : P.coeff D ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hL : L.natDegree ≤ D := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hi' : i < D := Finset.mem_range.mp hi
    calc
      (C (P.coeff i) * inclusivePowerSum i).natDegree ≤ (inclusivePowerSum i).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = i + 1 := (inclusive_power_sum_degree_leading i).1
      _ ≤ D := hi'
  have hH : H.natDegree = D + 1 := by
    dsimp [H]
    rw [Polynomial.natDegree_C_mul htop, (inclusive_power_sum_degree_leading D).1]
  have hlt : L.degree < H.degree := Polynomial.degree_lt_degree (by omega)
  have heq : inclusivePolynomialSum P = L + H := by
    exact Finset.sum_range_succ _ D
  constructor
  · rw [heq, Polynomial.natDegree_add_eq_right_of_natDegree_lt (by omega)]
    exact hH
  · rw [heq, Polynomial.leadingCoeff_add_of_degree_lt hlt]
    dsimp [H]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      (inclusive_power_sum_degree_leading D).2]
    rfl

theorem step_binomial_degree_leading (k m r : ℕ) (hm : 0 < m) :
    (stepBinomialPolynomial k m r).natDegree = k ∧
      (stepBinomialPolynomial k m r).leadingCoeff = (m : ℚ) ^ k / (k.factorial : ℚ) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hdeg : (C ((r + k : ℕ) : ℚ) + C (m : ℚ) * X).natDegree = 1 := by
    rw [Polynomial.natDegree_C_add, Polynomial.natDegree_C_mul_X _ hmQ]
  have hlc : (C ((r + k : ℕ) : ℚ) + C (m : ℚ) * X).leadingCoeff = (m : ℚ) := by
    rw [add_comm]
    exact Polynomial.leadingCoeff_linear hmQ
  constructor
  · simp only [stepBinomialPolynomial, Polynomial.natDegree_C_mul (inv_ne_zero hf),
      Polynomial.natDegree_comp, descPochhammer_natDegree, hdeg, mul_one]
  · rw [stepBinomialPolynomial, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_comp (by rw [hdeg]; norm_num),
      (monic_descPochhammer ℚ k), hlc, descPochhammer_natDegree]
    ring

theorem concrete_residue_degree_leading (d m r : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (concreteResiduePolynomial d m r).natDegree = 2 * d ∧
      (concreteResiduePolynomial d m r).leadingCoeff =
        1 / ((m : ℚ) * ((2 * d).factorial : ℚ)) := by
  let k := 2 * d - 1
  have hk : k + 1 = 2 * d := by dsimp [k]; omega
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hs := step_binomial_degree_leading k m r hm
  have hs0 : stepBinomialPolynomial k m r ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [hs.2]
    exact div_ne_zero (pow_ne_zero _ hmQ) (by exact_mod_cast Nat.factorial_ne_zero k)
  have hi := inclusive_polynomial_sum_degree_leading (stepBinomialPolynomial k m r) hs0
  have hdeg : (C ((m : ℚ)⁻¹) * (X - C (r : ℚ))).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hmQ), Polynomial.natDegree_sub_C,
      Polynomial.natDegree_X]
  have hlc : (C ((m : ℚ)⁻¹) * (X - C (r : ℚ))).leadingCoeff = (m : ℚ)⁻¹ := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_sub_C, mul_one]
  constructor
  · change ((inclusivePolynomialSum (stepBinomialPolynomial k m r)).comp _).natDegree = _
    rw [Polynomial.natDegree_comp, hdeg, mul_one, hi.1, hs.1, hk]
  · change ((inclusivePolynomialSum (stepBinomialPolynomial k m r)).comp _).leadingCoeff = _
    rw [Polynomial.leadingCoeff_comp (by rw [hdeg]; norm_num), hlc, hi.1, hi.2, hs.1, hs.2,
      ← hk, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hkQ : (k + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    rw [← mul_pow, one_div, mul_inv_cancel₀ hmQ, one_pow]

theorem concrete_polynomial_part_degree_leading (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (concretePolynomialPart d m).natDegree = 2 * d ∧
      (concretePolynomialPart d m).leadingCoeff =
        1 / ((m : ℚ) * ((2 * d).factorial : ℚ)) :=
  concrete_residue_degree_leading d m 0 hd hm

end PartitionLaguerre

#print axioms PartitionLaguerre.bernoulli_polynomial_degree_leading
#print axioms PartitionLaguerre.inclusive_power_sum_degree_leading
#print axioms PartitionLaguerre.inclusive_polynomial_sum_degree_leading
#print axioms PartitionLaguerre.step_binomial_degree_leading
#print axioms PartitionLaguerre.concrete_residue_degree_leading
#print axioms PartitionLaguerre.concrete_polynomial_part_degree_leading
