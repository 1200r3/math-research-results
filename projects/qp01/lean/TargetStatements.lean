import PartitionDefinitions

namespace PartitionLaguerre

def mainClassification : Prop :=
  ∀ d m : ℕ, 2 ≤ d → 2 ≤ m →
    (eventualPositiveThrough d (partitionCount d m) ↔
      Even d ∨ (Odd d ∧ m ≤ criticalIndex d))

def aboveThresholdFailure : Prop :=
  ∀ d m : ℕ, 2 ≤ d → 2 ≤ m → Odd d → criticalIndex d < m →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m ∣ n + 2 * d →
      laguerre d (partitionCount d m) n < 0

def leadingSignsClaim : Prop :=
  ∀ d m : ℕ, 2 ≤ d → 2 ≤ m →
    ((0 < leadingNumerator d m false ∧ 0 ≤ leadingNumerator d m true) ↔
      Even d ∨ (Odd d ∧ m ≤ criticalIndex d))

def criticalBetaClaim : Prop :=
  ∀ d : ℕ, 3 ≤ d → 0 < criticalBeta d

end PartitionLaguerre
