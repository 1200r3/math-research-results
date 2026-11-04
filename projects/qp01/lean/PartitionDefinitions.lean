import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

noncomputable section

namespace PartitionLaguerre

def partitionCount (d m n : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (n / m + 1),
    (((n - m * v + (2 * d - 1)).choose (2 * d - 1)) : ℚ)

def laguerre (j : ℕ) (f : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * j + 1),
    (-1 : ℚ) ^ (k + j) * ((2 * j).choose k : ℚ) *
      f (n + k) * f (n + (2 * j - k))

def eventualPositiveThrough (d : ℕ) (f : ℕ → ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ j : ℕ, 1 ≤ j → j ≤ d → 0 < laguerre j f n

def criticalIndex (d : ℕ) : ℕ := 1 + Nat.centralBinom d / 2

def leadingNumerator (d m : ℕ) (exceptional : Bool) : ℤ :=
  (Nat.centralBinom d : ℤ) +
    2 * (-1 : ℤ) ^ d * ((if exceptional then (m : ℤ) else 0) - 1)

def criticalB0 (m : ℝ) : ℝ := -(m - 1) / m

def criticalB2 (d m : ℝ) : ℝ :=
  (m - 1) / m * (-d ^ 2 + d * (2 * d - 1) * (m + 1) / 6)

def centeredSecond (d m a : ℝ) : ℝ :=
  -a * (2 * d) * (2 * d - 1) * (2 * d + m ^ 2) / 24

def betaExpression (d m a F C : ℝ) : ℝ :=
  a ^ 2 * F * C * d * (m ^ 2 - 4 * d ^ 2) / 12 +
    2 * a * (d * (2 * d - 1)) * criticalB2 d m +
    2 * centeredSecond d m a * criticalB0 m

def criticalBeta (d : ℕ) : ℝ :=
  let m : ℝ := criticalIndex d
  let F : ℝ := (2 * d).factorial
  betaExpression d m (1 / (m * F)) F (Nat.centralBinom d)

end PartitionLaguerre
