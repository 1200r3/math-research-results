import PolynomialPartDegree

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem desc_pochhammer_eval_reflection (k : ℕ) (x : ℚ) :
    (descPochhammer ℚ k).eval ((k : ℚ) - 1 - x) =
      (-1 : ℚ) ^ k * (descPochhammer ℚ k).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.cast_succ, add_sub_cancel_right]
    calc
      _ = ((k : ℚ) - x) * (descPochhammer ℚ k).eval ((k : ℚ) - 1 - x) := by
        rw [descPochhammer_succ_left]
        simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
          Polynomial.eval_sub, Polynomial.eval_one]
        congr 1
        ring
      _ = ((k : ℚ) - x) * ((-1 : ℚ) ^ k * (descPochhammer ℚ k).eval x) := by rw [ih]
      _ = _ := by
        rw [descPochhammer_succ_right]
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_natCast, pow_succ]
        ring

def partitionCenter (d m : ℕ) : ℚ := (2 * (d : ℚ) + (m : ℚ)) / 2

def centeredPolynomialPart (d m : ℕ) : ℚ[X] :=
  (concretePolynomialPart d m).comp (X - C (partitionCenter d m))

theorem centered_polynomial_step (d m : ℕ) (hm : 0 < m) (x : ℚ) :
    (centeredPolynomialPart d m).eval (x + (m : ℚ)) -
      (centeredPolynomialPart d m).eval x =
      (descPochhammer ℚ (2 * d - 1)).eval
        (x - partitionCenter d m + (m : ℚ) + ((2 * d - 1 : ℕ) : ℚ)) /
        ((2 * d - 1).factorial : ℚ) := by
  have h := concrete_residue_step d m 0 hm (x - partitionCenter d m)
  simp only [centeredPolynomialPart, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [show x + (m : ℚ) - partitionCenter d m =
    x - partitionCenter d m + (m : ℚ) by ring]
  exact h

theorem centered_increment_reflection (d m : ℕ) (hd : 1 ≤ d) (x : ℚ) :
    (descPochhammer ℚ (2 * d - 1)).eval
        ((-x - (m : ℚ)) - partitionCenter d m + (m : ℚ) + ((2 * d - 1 : ℕ) : ℚ)) /
        ((2 * d - 1).factorial : ℚ) =
      -( (descPochhammer ℚ (2 * d - 1)).eval
        (x - partitionCenter d m + (m : ℚ) + ((2 * d - 1 : ℕ) : ℚ)) /
        ((2 * d - 1).factorial : ℚ)) := by
  have hk : Odd (2 * d - 1) := by exact ⟨d - 1, by omega⟩
  have harg : (-x - (m : ℚ)) - partitionCenter d m + (m : ℚ) + ((2 * d - 1 : ℕ) : ℚ) =
      ((2 * d - 1 : ℕ) : ℚ) - 1 -
        (x - partitionCenter d m + (m : ℚ) + ((2 * d - 1 : ℕ) : ℚ)) := by
    rw [Nat.cast_sub (show 1 ≤ 2 * d by omega)]
    simp only [partitionCenter, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [harg, desc_pochhammer_eval_reflection, hk.neg_one_pow]
  ring

/-- The actual common polynomial becomes even about -(2d+m)/2. -/
theorem centered_polynomial_even (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m) :
    (centeredPolynomialPart d m).comp (C (-1) * X) = centeredPolynomialPart d m := by
  let S := centeredPolynomialPart d m
  let Q := S - S.comp (C (-1) * X)
  have hp : ∀ x : ℚ, Q.eval (x + (m : ℚ)) = Q.eval x := by
    intro x
    have h1 := centered_polynomial_step d m hm x
    have h2 := centered_polynomial_step d m hm (-x - (m : ℚ))
    rw [show -x - (m : ℚ) + (m : ℚ) = -x by ring,
      centered_increment_reflection d m hd x] at h2
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [show (-1 : ℚ) * (x + (m : ℚ)) = -x - (m : ℚ) by ring,
      show (-1 : ℚ) * x = -x by ring]
    change S.eval (x + (m : ℚ)) - S.eval (-x - (m : ℚ)) = S.eval x - S.eval (-x)
    linarith
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hc := polynomial_constant_of_nonzero_period Q (m : ℚ) hmQ hp
  have hz : Q.eval 0 = 0 := by simp [Q]
  rw [hz, Polynomial.C_0] at hc
  exact (sub_eq_zero.mp hc).symm

theorem centered_polynomial_odd_coefficient_zero (d m i : ℕ) (hd : 1 ≤ d) (hm : 0 < m)
    (hi : Odd i) : (centeredPolynomialPart d m).coeff i = 0 := by
  have h := congrArg (fun P : ℚ[X] => P.coeff i) (centered_polynomial_even d m hd hm)
  rw [Polynomial.comp_C_mul_X_coeff, hi.neg_one_pow] at h
  linarith

end PartitionLaguerre

#print axioms PartitionLaguerre.desc_pochhammer_eval_reflection
#print axioms PartitionLaguerre.centered_polynomial_step
#print axioms PartitionLaguerre.centered_increment_reflection
#print axioms PartitionLaguerre.centered_polynomial_even
#print axioms PartitionLaguerre.centered_polynomial_odd_coefficient_zero
