import ConcretePartitionModel

noncomputable section

namespace PartitionLaguerre

open Polynomial

/-- Every branch is an antidifference, with the same step-m increment. -/
theorem concrete_residue_step (d m r : ℕ) (hm : 0 < m) (x : ℚ) :
    (concreteResiduePolynomial d m r).eval (x + (m : ℚ)) -
      (concreteResiduePolynomial d m r).eval x =
      (descPochhammer ℚ (2 * d - 1)).eval (x + (m : ℚ) + ((2 * d - 1 : ℕ) : ℚ)) /
        ((2 * d - 1).factorial : ℚ) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  let k : ℕ := 2 * d - 1
  let u : ℚ := (m : ℚ)⁻¹ * (x - (r : ℚ))
  have hu : (m : ℚ)⁻¹ * (x + (m : ℚ) - (r : ℚ)) = u + 1 := by
    dsimp [u]
    field_simp [hmQ]
    ring
  have hs := congrArg (fun P : ℚ[X] => P.eval u)
    (inclusive_polynomial_sum_step (stepBinomialPolynomial k m r))
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one] at hs
  simp only [concreteResiduePolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [hu]
  change (inclusivePolynomialSum (stepBinomialPolynomial k m r)).eval (u + 1) -
    (inclusivePolynomialSum (stepBinomialPolynomial k m r)).eval u = _
  rw [hs]
  simp only [stepBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  have harg : ((r + k : ℕ) : ℚ) + (m : ℚ) * (u + 1) = x + (m : ℚ) + (k : ℚ) := by
    dsimp [u]
    push_cast
    field_simp [hmQ]
    ring
  rw [harg]
  change ((k.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ k).eval (x + (m : ℚ) + (k : ℚ)) = _
  rw [div_eq_mul_inv, mul_comm]

/-- The nonconstant part is common to every branch. This is proved from the
exact construction, not supplied as a representation hypothesis. -/
theorem concrete_residue_common_part (d m r : ℕ) (hm : 0 < m) :
    concreteResiduePolynomial d m r = concreteResiduePolynomial d m 0 +
      C ((concreteResiduePolynomial d m r).eval 0 -
        (concreteResiduePolynomial d m 0).eval 0) := by
  let Q : ℚ[X] := concreteResiduePolynomial d m r - concreteResiduePolynomial d m 0
  have hperiod : ∀ x : ℚ, Q.eval (x + (m : ℚ)) = Q.eval x := by
    intro x
    have hr := concrete_residue_step d m r hm x
    have h0 := concrete_residue_step d m 0 hm x
    simp only [Q, Polynomial.eval_sub]
    linarith
  have hconst := polynomial_constant_of_nonzero_period Q (m : ℚ)
    (by exact_mod_cast (Nat.ne_of_gt hm)) hperiod
  have heq : concreteResiduePolynomial d m r - concreteResiduePolynomial d m 0 =
      C ((concreteResiduePolynomial d m r).eval 0 -
        (concreteResiduePolynomial d m 0).eval 0) := by
    simpa only [Q, Polynomial.eval_sub] using hconst
  calc
    concreteResiduePolynomial d m r =
        (concreteResiduePolynomial d m r - concreteResiduePolynomial d m 0) +
          concreteResiduePolynomial d m 0 := (sub_add_cancel _ _).symm
    _ = C ((concreteResiduePolynomial d m r).eval 0 -
        (concreteResiduePolynomial d m 0).eval 0) +
          concreteResiduePolynomial d m 0 := by rw [heq]
    _ = _ := add_comm _ _

def concretePolynomialPart (d m : ℕ) : ℚ[X] := concreteResiduePolynomial d m 0

def concretePeriodicConstant (d m r : ℕ) : ℚ :=
  (concreteResiduePolynomial d m r).eval 0 - (concretePolynomialPart d m).eval 0

theorem partition_count_common_polynomial_part (d m n : ℕ) (hm : 0 < m) :
    partitionCount d m n = (concretePolynomialPart d m).eval (n : ℚ) +
      concretePeriodicConstant d m (n % m) := by
  rw [concrete_partition_representation d m n hm,
    concrete_residue_common_part d m (n % m) hm, Polynomial.eval_add,
    Polynomial.eval_C]
  rfl

end PartitionLaguerre

#print axioms PartitionLaguerre.concrete_residue_step
#print axioms PartitionLaguerre.concrete_residue_common_part
#print axioms PartitionLaguerre.partition_count_common_polynomial_part
