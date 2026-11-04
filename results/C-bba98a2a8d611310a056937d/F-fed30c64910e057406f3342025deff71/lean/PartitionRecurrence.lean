import ConcretePartitionModel

noncomputable section

namespace PartitionLaguerre

/-- General binomial order, so successive ordinary differences lower the
number of colored unit parts one at a time. -/
def coloredPartition (q m n : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (n / m + 1), (((n - m * v + q).choose q : ℕ) : ℚ)

theorem colored_partition_zero (m n : ℕ) :
    coloredPartition 0 m n = (n / m + 1 : ℕ) := by
  simp [coloredPartition]

theorem colored_partition_step (q m n : ℕ) :
    coloredPartition (q + 1) m (n + 1) - coloredPartition (q + 1) m n =
      coloredPartition q m (n + 1) := by
  have hterm : ∀ v ∈ Finset.range (n / m + 1),
      ((((n + 1 - m * v + (q + 1)).choose (q + 1) : ℕ) : ℚ)) =
        (((n - m * v + (q + 1)).choose (q + 1) : ℕ) : ℚ) +
        (((n + 1 - m * v + q).choose q : ℕ) : ℚ) := by
    intro v hv
    have hv' : v ≤ n / m := by have := Finset.mem_range.mp hv; omega
    have hmv : m * v ≤ n :=
      (Nat.mul_le_mul_left m hv').trans (Nat.mul_div_le n m)
    have he : n + 1 - m * v + (q + 1) = (n - m * v + q + 1) + 1 := by omega
    have he' : n + 1 - m * v + q = n - m * v + q + 1 := by omega
    rw [he, he', Nat.choose_succ_succ', Nat.cast_add]
    rw [add_comm]
    congr 2
  have hsum :
      (∑ v ∈ Finset.range (n / m + 1),
        (((n + 1 - m * v + (q + 1)).choose (q + 1) : ℕ) : ℚ)) =
      coloredPartition (q + 1) m n +
        ∑ v ∈ Finset.range (n / m + 1),
          (((n + 1 - m * v + q).choose q : ℕ) : ℚ) := by
    calc
      _ = ∑ v ∈ Finset.range (n / m + 1),
          ((((n - m * v + (q + 1)).choose (q + 1) : ℕ) : ℚ) +
            (((n + 1 - m * v + q).choose q : ℕ) : ℚ)) :=
        Finset.sum_congr rfl hterm
      _ = _ := Finset.sum_add_distrib
  by_cases hdiv : m ∣ n + 1
  · have hquot := Nat.succ_div_of_dvd hdiv
    have hnew : n + 1 - m * (n / m + 1) = 0 := by
      rw [← hquot, Nat.mul_div_cancel' hdiv, Nat.sub_self]
    have hextra (s : ℕ) : coloredPartition s m (n + 1) =
        (∑ v ∈ Finset.range (n / m + 1),
          (((n + 1 - m * v + s).choose s : ℕ) : ℚ)) + 1 := by
      unfold coloredPartition
      rw [hquot, Finset.sum_range_succ, hnew]
      simp
    rw [hextra (q + 1), hextra q, hsum]
    ring
  · have hquot := Nat.succ_div_of_not_dvd hdiv
    unfold coloredPartition at *
    rw [hquot] at *
    linarith [hsum]

theorem colored_partition_zero_step (m n : ℕ) :
    coloredPartition 0 m (n + 1) - coloredPartition 0 m n =
      if m ∣ n + 1 then 1 else 0 := by
  rw [colored_partition_zero, colored_partition_zero, Nat.succ_div]
  split_ifs <;> push_cast <;> ring

theorem partition_count_eq_colored (d m n : ℕ) :
    partitionCount d m n = coloredPartition (2 * d - 1) m n := rfl

end PartitionLaguerre

#print axioms PartitionLaguerre.colored_partition_zero
#print axioms PartitionLaguerre.colored_partition_step
#print axioms PartitionLaguerre.colored_partition_zero_step
#print axioms PartitionLaguerre.partition_count_eq_colored
