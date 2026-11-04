import CyclicDifference

noncomputable section

namespace PartitionLaguerre

def cyclicGreenValue (m t : ℕ) : ℚ :=
  -((m : ℚ) ^ 2 - 1) / (12 * (m : ℚ)) +
    (t : ℚ) * ((m : ℚ) - (t : ℚ)) / (2 * (m : ℚ))

def cyclicGreenSequence (m n : ℕ) : ℚ := cyclicGreenValue m (n % m)

theorem cyclic_green_period (m n : ℕ) :
    cyclicGreenSequence m (n + m) = cyclicGreenSequence m n := by
  simp [cyclicGreenSequence]

theorem rational_sum_range_first (m : ℕ) :
    (∑ t ∈ Finset.range m, (t : ℚ)) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

theorem rational_sum_range_second (m : ℕ) :
    (∑ t ∈ Finset.range m, (t : ℚ) ^ 2) =
      (m : ℚ) * ((m : ℚ) - 1) * (2 * (m : ℚ) - 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

theorem cyclic_green_zero_mean (m : ℕ) (hm : 0 < m) :
    (∑ t ∈ Finset.range m, cyclicGreenValue m t) = 0 := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  calc
    _ = (m : ℚ) * (-((m : ℚ) ^ 2 - 1) / (12 * (m : ℚ))) +
        ((∑ t ∈ Finset.range m, (t : ℚ)) * (m : ℚ) -
          ∑ t ∈ Finset.range m, (t : ℚ) ^ 2) / (2 * (m : ℚ)) := by
      simp only [cyclicGreenValue, mul_sub, Finset.sum_add_distrib,
        ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, pow_two]
      ring
    _ = 0 := by
      rw [rational_sum_range_first, rational_sum_range_second]
      field_simp
      ring

theorem cyclic_green_sequence_zero_mean (m : ℕ) (hm : 0 < m) :
    (∑ t ∈ Finset.range m, cyclicGreenSequence m t) = 0 := by
  calc
    _ = ∑ t ∈ Finset.range m, cyclicGreenValue m t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact congrArg (cyclicGreenValue m) (Nat.mod_eq_of_lt (Finset.mem_range.mp ht))
    _ = 0 := cyclic_green_zero_mean m hm

/-- Exact cyclic second difference, including both wraparound cases. -/
theorem cyclic_green_second_difference (m n : ℕ) (hm : 2 ≤ m) :
    cyclicGreenSequence m (n + 2) - 2 * cyclicGreenSequence m (n + 1) +
      cyclicGreenSequence m n = (if m ∣ n + 1 then 1 else 0) - 1 / (m : ℚ) := by
  let t := n % m
  have ht : t < m := Nat.mod_lt n (by omega)
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmod1 : (n + 1) % m = (t + 1) % m := by simp [t, Nat.add_mod]
  have hmod2 : (n + 2) % m = (t + 2) % m := by simp [t, Nat.add_mod]
  unfold cyclicGreenSequence
  simp only [Nat.dvd_iff_mod_eq_zero, hmod1, hmod2]
  change cyclicGreenValue m ((t + 2) % m) - 2 * cyclicGreenValue m ((t + 1) % m) +
    cyclicGreenValue m t = (if (t + 1) % m = 0 then 1 else 0) - 1 / (m : ℚ)
  by_cases ht1 : t + 1 = m
  · have he : t + 2 = m + 1 := by omega
    have hlast : (t + 2) % m = 1 := by
      simp [he, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < m by omega)]
    rw [hlast, ht1, Nat.mod_self, if_pos rfl, show t = m - 1 by omega]
    simp only [cyclicGreenValue, Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one,
      Nat.cast_zero]
    field_simp
    ring
  · by_cases ht2 : t + 2 = m
    · have hlt1 : t + 1 < m := by omega
      rw [ht2, Nat.mod_self, Nat.mod_eq_of_lt hlt1, if_neg (by omega),
        show t = m - 2 by omega]
      simp only [cyclicGreenValue, Nat.cast_sub hm, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero]
      field_simp
      ring
    · have hlt2 : t + 2 < m := by omega
      rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt (show t + 1 < m by omega),
        if_neg (by omega)]
      simp only [cyclicGreenValue, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      field_simp
      ring

end PartitionLaguerre

#print axioms PartitionLaguerre.cyclic_green_period
#print axioms PartitionLaguerre.rational_sum_range_first
#print axioms PartitionLaguerre.rational_sum_range_second
#print axioms PartitionLaguerre.cyclic_green_zero_mean
#print axioms PartitionLaguerre.cyclic_green_sequence_zero_mean
#print axioms PartitionLaguerre.cyclic_green_second_difference
