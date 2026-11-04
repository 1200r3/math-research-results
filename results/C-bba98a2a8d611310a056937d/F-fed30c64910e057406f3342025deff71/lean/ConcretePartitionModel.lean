import ResidueDefinitions
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Roots
import Lean.Elab.Tactic.Omega

noncomputable section

namespace PartitionLaguerre

open Polynomial

/-- Exact polynomial for the inclusive sum of k-th powers, using Faulhaber. -/
def inclusivePowerSum (k : ℕ) : ℚ[X] :=
  C ((k + 1 : ℚ)⁻¹) *
    ((Polynomial.bernoulli (k + 1)).comp (X + 1) - C (_root_.bernoulli (k + 1)))

theorem inclusive_power_sum_eval (k t : ℕ) :
    (inclusivePowerSum k).eval (t : ℚ) =
      ∑ u ∈ Finset.range (t + 1), (u : ℚ) ^ k := by
  have h := Polynomial.sum_range_pow_eq_bernoulli_sub (t + 1) k
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp only [inclusivePowerSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  rw [← h]
  have hden : (k + 1 : ℚ) ≠ 0 := by positivity
  exact inv_mul_cancel_left₀ hden _

/-- Summation of an arbitrary rational polynomial over 0,...,t. -/
def inclusivePolynomialSum (P : ℚ[X]) : ℚ[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), C (P.coeff i) * inclusivePowerSum i

theorem inclusive_polynomial_sum_eval (P : ℚ[X]) (t : ℕ) :
    (inclusivePolynomialSum P).eval (t : ℚ) =
      ∑ u ∈ Finset.range (t + 1), P.eval (u : ℚ) := by
  calc
    (inclusivePolynomialSum P).eval (t : ℚ) =
        ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ∑ u ∈ Finset.range (t + 1), (u : ℚ) ^ i := by
      simp only [inclusivePolynomialSum, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, inclusive_power_sum_eval]
    _ = ∑ u ∈ Finset.range (t + 1),
        ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (u : ℚ) ^ i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ u ∈ Finset.range (t + 1), P.eval (u : ℚ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (Polynomial.eval_eq_sum_range (p := P) (u : ℚ)).symm

/-- Polynomial whose natural values are choose(r + m*t + k,k). -/
def stepBinomialPolynomial (k m r : ℕ) : ℚ[X] :=
  C ((k.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ k).comp (C ((r + k : ℕ) : ℚ) + C (m : ℚ) * X)

theorem step_binomial_polynomial_eval (k m r t : ℕ) :
    (stepBinomialPolynomial k m r).eval (t : ℚ) =
      (((r + m * t + k).choose k : ℕ) : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div ℚ]
  simp only [stepBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  have harg : ((r + k : ℕ) : ℚ) + (m : ℚ) * (t : ℚ) =
      ((r + m * t + k : ℕ) : ℚ) := by
    push_cast
    ring
  rw [harg, div_eq_mul_inv, mul_comm]

/-- Reverse the finite partition sum. All natural subtractions are justified
on the actual summation range; no extension to negative integers is used. -/
theorem partition_count_reindexed (d m n : ℕ) :
    partitionCount d m n =
      ∑ u ∈ Finset.range (n / m + 1),
        ((((n % m + m * u + (2 * d - 1)).choose (2 * d - 1)) : ℕ) : ℚ) := by
  unfold partitionCount
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u ≤ n / m := by
    have := Finset.mem_range.mp hu
    omega
  have he : n = n % m + m * (n / m) := (Nat.mod_add_div n m).symm
  have hmul : m * (n / m - u) + m * u = m * (n / m) := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hu']
  have hpred : n / m + 1 - 1 - u = n / m - u := by omega
  have hsub : n - m * (n / m + 1 - 1 - u) = n % m + m * u := by
    rw [hpred]
    omega
  rw [hsub]

/-- A concrete rational branch polynomial for the exact partition sequence. -/
def concreteResiduePolynomial (d m r : ℕ) : ℚ[X] :=
  (inclusivePolynomialSum (stepBinomialPolynomial (2 * d - 1) m r)).comp
    (C ((m : ℚ)⁻¹) * (X - C (r : ℚ)))

theorem concrete_partition_representation (d m n : ℕ) (hm : 0 < m) :
    partitionCount d m n =
      (concreteResiduePolynomial d m (n % m)).eval (n : ℚ) := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have he : (m : ℚ) * ((n / m : ℕ) : ℚ) + ((n % m : ℕ) : ℚ) = (n : ℚ) := by
    exact_mod_cast Nat.div_add_mod n m
  have harg : (m : ℚ)⁻¹ * ((n : ℚ) - ((n % m : ℕ) : ℚ)) =
      ((n / m : ℕ) : ℚ) := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_eq_iff hmQ).mpr
    linarith
  symm
  simp only [concreteResiduePolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [harg, inclusive_polynomial_sum_eval]
  simp_rw [step_binomial_polynomial_eval]
  exact (partition_count_reindexed d m n).symm

/-- Equality at every natural input determines a rational polynomial. -/
theorem polynomial_eq_of_nat_eval (P Q : ℚ[X])
    (h : ∀ n : ℕ, P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (n : ℚ)) := Nat.cast_injective
  refine (Set.infinite_range_of_injective hi).mono ?_
  rintro x ⟨n, rfl⟩
  exact h n

theorem inclusive_polynomial_sum_step (P : ℚ[X]) :
    (inclusivePolynomialSum P).comp (X + 1) - inclusivePolynomialSum P =
      P.comp (X + 1) := by
  apply polynomial_eq_of_nat_eval
  intro t
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  have ht : (t : ℚ) + 1 = ((t + 1 : ℕ) : ℚ) := by push_cast; rfl
  rw [ht, inclusive_polynomial_sum_eval, inclusive_polynomial_sum_eval,
    Finset.sum_range_succ]
  ring

/-- A nonzero rational period forces a polynomial to be constant. -/
theorem polynomial_constant_of_nonzero_period (P : ℚ[X]) (m : ℚ) (hm : m ≠ 0)
    (hperiod : ∀ x : ℚ, P.eval (x + m) = P.eval x) :
    P = C (P.eval 0) := by
  have horbit : ∀ n : ℕ, P.eval ((n : ℚ) * m) = P.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hperiod, ih]
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => (n : ℚ) * m) := by
    intro a b hab
    exact Nat.cast_injective (mul_right_cancel₀ hm hab)
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨n, rfl⟩
  simpa only [Set.mem_setOf_eq, Polynomial.eval_C] using horbit n

end PartitionLaguerre

#print axioms PartitionLaguerre.inclusive_power_sum_eval
#print axioms PartitionLaguerre.inclusive_polynomial_sum_eval
#print axioms PartitionLaguerre.step_binomial_polynomial_eval
#print axioms PartitionLaguerre.partition_count_reindexed
#print axioms PartitionLaguerre.concrete_partition_representation
#print axioms PartitionLaguerre.polynomial_eq_of_nat_eval
#print axioms PartitionLaguerre.inclusive_polynomial_sum_step
#print axioms PartitionLaguerre.polynomial_constant_of_nonzero_period
