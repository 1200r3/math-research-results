import PartitionRecurrence
import Mathlib.Algebra.Group.ForwardDiff

noncomputable section

namespace PartitionLaguerre

theorem colored_partition_iterated_difference (q m n : ℕ) :
    ((fwdDiff (1 : ℕ))^[q + 1]) (coloredPartition q m) n =
      if m ∣ n + (q + 1) then 1 else 0 := by
  induction q generalizing n with
  | zero =>
    simpa only [Function.iterate_one, fwdDiff, Nat.zero_add] using
      colored_partition_zero_step m n
  | succ q ih =>
    have hdiff : fwdDiff (1 : ℕ) (coloredPartition (q + 1) m) =
        fun x => coloredPartition q m (x + 1) := by
      funext x
      exact colored_partition_step q m x
    rw [Function.iterate_succ_apply, hdiff,
      fwdDiff_iter_comp_add (1 : ℕ) (coloredPartition q m) 1 (q + 1) n, ih]
    congr 2 <;> omega

/-- The full ordinary difference of the actual partition count is exactly
the stated exceptional residue indicator, including its forward shift. -/
theorem partition_count_iterated_difference (d m n : ℕ) (hd : 1 ≤ d) :
    ((fwdDiff (1 : ℕ))^[2 * d]) (partitionCount d m) n =
      if m ∣ n + 2 * d then 1 else 0 := by
  have hk : 2 * d - 1 + 1 = 2 * d := by omega
  have h := colored_partition_iterated_difference (2 * d - 1) m n
  rw [hk] at h
  exact h

end PartitionLaguerre

#print axioms PartitionLaguerre.colored_partition_iterated_difference
#print axioms PartitionLaguerre.partition_count_iterated_difference
