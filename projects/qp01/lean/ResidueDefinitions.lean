import PartitionDefinitions
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Interval.Finset.Nat

noncomputable section

namespace PartitionLaguerre

open Polynomial

def residueSequence (M : ℕ) (F : ℕ → ℚ[X]) (n : ℕ) : ℚ :=
  (F (n % M)).eval (n : ℚ)

def residueTransform (M j : ℕ) (F : ℕ → ℚ[X]) (r : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (2 * j + 1),
    C ((-1 : ℚ) ^ (k + j) * ((2 * j).choose k : ℚ)) *
      (F ((r + k) % M)).comp (X + C (k : ℚ)) *
      (F ((r + (2 * j - k)) % M)).comp (X + C ((2 * j - k : ℕ) : ℚ))

def lowerCoefficientMass (P : ℚ[X]) : ℚ :=
  ∑ i ∈ Finset.range P.natDegree, |P.coeff i|

def coefficientBound (P : ℚ[X]) : ℕ :=
  1 + Nat.ceil (lowerCoefficientMass P / |P.leadingCoeff|)

def uniformResidueBound (M d : ℕ) (F : ℕ → ℚ[X]) : ℕ :=
  max 1 ((Finset.Icc 1 d).sup fun j =>
    (Finset.range M).sup fun r => coefficientBound (residueTransform M j F r))

end PartitionLaguerre
