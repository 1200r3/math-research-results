import ResidueEvaluation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace PartitionLaguerre

open Polynomial

theorem polynomial_positive_bound : polynomialPositiveBoundClaim := by
  intro P hLC x hx
  have hbNat : 1 ≤ coefficientBound P := by
    unfold coefficientBound
    omega
  have hb : (1 : ℚ) ≤ (coefficientBound P : ℚ) := by exact_mod_cast hbNat
  have hx1 : (1 : ℚ) ≤ x := hb.trans hx
  have hx0 : (0 : ℚ) < x := by linarith
  by_cases hk : P.natDegree = 0
  · have heval : P.eval x = P.leadingCoeff := by
      calc
        P.eval x = (C (P.coeff 0)).eval x :=
          congrArg (fun Q : ℚ[X] => Q.eval x) (eq_C_of_natDegree_eq_zero hk)
        _ = P.coeff 0 := by rw [eval_C]
        _ = P.leadingCoeff := by
          simpa only [hk] using (show P.coeff P.natDegree = P.leadingCoeff from rfl)
    rw [heval]
    exact hLC
  have hceil : lowerCoefficientMass P / |P.leadingCoeff| < (coefficientBound P : ℚ) := by
    have h := Nat.le_ceil (lowerCoefficientMass P / |P.leadingCoeff|)
    unfold coefficientBound
    push_cast
    linarith
  have hratio := hceil.trans_le hx
  rw [abs_of_pos hLC] at hratio
  have hmass : lowerCoefficientMass P < P.leadingCoeff * x := by
    simpa only [mul_comm] using (div_lt_iff₀ hLC).mp hratio
  have habs : |∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i| ≤
      lowerCoefficientMass P * x ^ (P.natDegree - 1) := by
    calc
      |∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i|
          ≤ ∑ i ∈ Finset.range P.natDegree, |P.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range P.natDegree, |P.coeff i| * x ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0.le i)]
      _ ≤ ∑ i ∈ Finset.range P.natDegree, |P.coeff i| * x ^ (P.natDegree - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ P.natDegree - 1 := by
          have := Finset.mem_range.mp hi
          omega
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hi') (abs_nonneg _)
      _ = lowerCoefficientMass P * x ^ (P.natDegree - 1) := by
        rw [← Finset.sum_mul]
        rfl
  have hlow : -(∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i) ≤
      lowerCoefficientMass P * x ^ (P.natDegree - 1) :=
    (neg_le_abs _).trans habs
  have hstrict : lowerCoefficientMass P * x ^ (P.natDegree - 1) <
      P.leadingCoeff * x ^ P.natDegree := by
    calc
      lowerCoefficientMass P * x ^ (P.natDegree - 1)
          < (P.leadingCoeff * x) * x ^ (P.natDegree - 1) :=
        mul_lt_mul_of_pos_right hmass (pow_pos hx0 _)
      _ = P.leadingCoeff * x ^ P.natDegree := by
        have hk' : P.natDegree = (P.natDegree - 1) + 1 := by omega
        conv_rhs => rw [hk', pow_succ]
        ring
  rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree]
  linarith

theorem coefficient_bound_neg (P : ℚ[X]) : coefficientBound (-P) = coefficientBound P := by
  simp [coefficientBound, lowerCoefficientMass]

theorem polynomial_negative_bound : polynomialNegativeBoundClaim := by
  intro P hLC x hx
  have hneg : 0 < (-P).leadingCoeff := by
    simpa only [leadingCoeff_neg, neg_pos] using hLC
  have hpos := polynomial_positive_bound (-P) hneg x
    (by simpa only [coefficient_bound_neg] using hx)
  simpa only [eval_neg, neg_pos] using hpos

theorem uniform_residue_positive : uniformResiduePositiveClaim := by
  intro M hM d F hLC n hn j hj hjd
  rw [residue_evaluation M hM F j n]
  apply polynomial_positive_bound
  · exact hLC j hj hjd (n % M) (Nat.mod_lt n hM)
  · have hr : n % M ∈ Finset.range M := Finset.mem_range.mpr (Nat.mod_lt n hM)
    have hjmem : j ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨hj, hjd⟩
    have hrbound : coefficientBound (residueTransform M j F (n % M)) ≤
        (Finset.range M).sup (fun r => coefficientBound (residueTransform M j F r)) :=
      Finset.le_sup (f := fun r => coefficientBound (residueTransform M j F r)) hr
    have hjbound : (Finset.range M).sup (fun r => coefficientBound (residueTransform M j F r)) ≤
        (Finset.Icc 1 d).sup (fun s =>
          (Finset.range M).sup (fun r => coefficientBound (residueTransform M s F r))) :=
      Finset.le_sup (f := fun s =>
        (Finset.range M).sup (fun r => coefficientBound (residueTransform M s F r))) hjmem
    have hbound : coefficientBound (residueTransform M j F (n % M)) ≤ n :=
      hrbound.trans (hjbound.trans ((le_max_right _ _).trans hn))
    exact_mod_cast hbound

end PartitionLaguerre

#print axioms PartitionLaguerre.polynomial_positive_bound
#print axioms PartitionLaguerre.polynomial_negative_bound
#print axioms PartitionLaguerre.uniform_residue_positive
