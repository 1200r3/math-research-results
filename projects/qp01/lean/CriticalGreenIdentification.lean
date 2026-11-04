import CyclicGreen

noncomputable section

namespace PartitionLaguerre

theorem periodic_green_identification (b : ℕ → ℚ) (q m : ℕ)
    (hq : 3 ≤ q) (hm : 2 ≤ m) (hp : ∀ n, b (n + m) = b n)
    (hD : ∀ n, ((fwdDiff (1 : ℕ))^[q]) b n =
      (if m ∣ n + q then 1 else 0) - 1 / (m : ℚ)) :
    ((fwdDiff (1 : ℕ))^[q - 2]) b =
      fun n => cyclicGreenSequence m (n + (q - 1)) := by
  apply periodic_second_difference_unique _ _ m (by omega)
  · exact iterated_difference_preserves_period b m (q - 2) hp
  · intro n
    rw [show n + m + (q - 1) = (n + (q - 1)) + m by omega,
      cyclic_green_period]
  · intro n
    have hb : ((fwdDiff (1 : ℕ))^[q - 2]) b (n + 2) -
        2 * ((fwdDiff (1 : ℕ))^[q - 2]) b (n + 1) +
          ((fwdDiff (1 : ℕ))^[q - 2]) b n =
        (if m ∣ n + q then 1 else 0) - 1 / (m : ℚ) := by
      calc
        _ = ((fwdDiff (1 : ℕ))^[q]) b n := by
          rw [← iterated_second_difference, show q - 2 + 2 = q by omega]
        _ = _ := hD n
    have hg := cyclic_green_second_difference m (n + (q - 1)) hm
    rw [show n + (q - 1) + 2 = (n + 2) + (q - 1) by omega,
      show n + (q - 1) + 1 = (n + 1) + (q - 1) by omega] at hg
    have he : (n + 1) + (q - 1) = n + q := by omega
    rw [← he] at hb
    linarith
  · have hb := periodic_iterated_difference_zero_mean b m (q - 3) hp
    rw [show q - 3 + 1 = q - 2 by omega] at hb
    have hg : (∑ n ∈ Finset.range m, cyclicGreenSequence m (n + (q - 1))) = 0 := by
      rw [periodic_sum_shift (cyclicGreenSequence m) m (q - 1) (cyclic_green_period m)]
      exact cyclic_green_sequence_zero_mean m (by omega)
    exact hb.trans hg.symm

theorem concrete_periodic_penultimate_difference (d m n : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m) :
    ((fwdDiff (1 : ℕ))^[2 * d - 2]) (concretePeriodicSequence d m) n =
      cyclicGreenSequence m (n + (2 * d - 1)) := by
  have h := periodic_green_identification (concretePeriodicSequence d m) (2 * d) m
    (by omega) hm (concrete_periodic_sequence_period d m)
    (fun n => concrete_periodic_full_difference d m n (by omega) (by omega))
  exact congrFun h n

theorem concrete_penultimate_exceptional_value (d m n : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (hr : m ∣ n + 2 * d) :
    ((fwdDiff (1 : ℕ))^[2 * d - 2]) (concretePeriodicSequence d m) (n + 1) =
      -((m : ℚ) ^ 2 - 1) / (12 * (m : ℚ)) := by
  rw [concrete_periodic_penultimate_difference d m (n + 1) hd hm,
    show n + 1 + (2 * d - 1) = n + 2 * d by omega]
  simp only [cyclicGreenSequence, Nat.mod_eq_zero_of_dvd hr, cyclicGreenValue,
    Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]

theorem concrete_preceding_exceptional_value (d m n : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (hr : m ∣ n + 2 * d) :
    ((fwdDiff (1 : ℕ))^[2 * d - 1]) (concretePeriodicSequence d m) (n + 1) =
      ((m : ℚ) - 1) / (2 * (m : ℚ)) := by
  rw [show 2 * d - 1 = (2 * d - 2) + 1 by omega, Function.iterate_succ_apply']
  simp only [fwdDiff]
  rw [show n + 1 + 1 = n + 2 by omega,
    concrete_periodic_penultimate_difference d m (n + 2) hd hm,
    concrete_periodic_penultimate_difference d m (n + 1) hd hm,
    show n + 2 + (2 * d - 1) = n + 2 * d + 1 by omega,
    show n + 1 + (2 * d - 1) = n + 2 * d by omega]
  have hmod : (n + 2 * d + 1) % m = 1 := by
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hr, Nat.mod_eq_of_lt (show 1 < m by omega)]
  simp only [cyclicGreenSequence, hmod, Nat.mod_eq_zero_of_dvd hr, cyclicGreenValue,
    Nat.cast_zero, Nat.cast_one]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp
  ring

end PartitionLaguerre

#print axioms PartitionLaguerre.periodic_green_identification
#print axioms PartitionLaguerre.concrete_periodic_penultimate_difference
#print axioms PartitionLaguerre.concrete_penultimate_exceptional_value
#print axioms PartitionLaguerre.concrete_preceding_exceptional_value
