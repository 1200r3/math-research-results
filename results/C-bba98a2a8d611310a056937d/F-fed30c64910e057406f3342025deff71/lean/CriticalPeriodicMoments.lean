import CriticalGreenIdentification
import DifferenceProduct

noncomputable section

namespace PartitionLaguerre

def periodicCenteredMoment (d h : ℕ) (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * d + 1),
    laguerreWeight d k * ((k : ℚ) - (d : ℚ)) ^ h * b (n + k)

theorem periodic_centered_moment_one (d n : ℕ) (hd : 1 ≤ d) (b : ℕ → ℚ) :
    periodicCenteredMoment d 1 b n = (-1 : ℚ) ^ d *
      (-(d : ℚ) * ((fwdDiff (1 : ℕ))^[2 * d]) b n +
        (2 * (d : ℚ)) * ((fwdDiff (1 : ℕ))^[2 * d - 1]) b (n + 1)) := by
  let c : ℚ := -(n : ℚ) - (d : ℚ)
  have heq : periodicCenteredMoment d 1 b n =
      ∑ k ∈ Finset.range (2 * d + 1),
        laguerreWeight d k * (((n + k : ℕ) : ℚ) + c) * b (n + k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [pow_one, Nat.cast_add]
    dsimp [c]
    ring
  have hp := iterated_difference_linear_product b c (2 * d - 1) n
  rw [show 2 * d - 1 + 1 = 2 * d by omega] at hp
  rw [Nat.cast_sub (show 1 ≤ 2 * d by omega)] at hp
  push_cast at hp
  rw [heq]
  have hw := laguerre_weighted_sequence_sum d n (fun t => ((t : ℚ) + c) * b t)
  have hsum : (∑ k ∈ Finset.range (2 * d + 1),
      laguerreWeight d k * (((n + k : ℕ) : ℚ) + c) * b (n + k)) =
      (-1 : ℚ) ^ d * ((fwdDiff (1 : ℕ))^[2 * d]) (fun t => ((t : ℚ) + c) * b t) n := by
    simpa only [mul_assoc] using hw
  rw [hsum, hp]
  dsimp [c]
  ring

theorem periodic_centered_moment_two (d n : ℕ) (hd : 1 ≤ d) (b : ℕ → ℚ) :
    periodicCenteredMoment d 2 b n = (-1 : ℚ) ^ d *
      ((d : ℚ) ^ 2 * ((fwdDiff (1 : ℕ))^[2 * d]) b n +
        (2 * (d : ℚ)) * (2 * (d : ℚ) - 1) *
          ((fwdDiff (1 : ℕ))^[2 * d - 2]) b (n + 1)) := by
  let c : ℚ := -(n : ℚ) - (d : ℚ)
  have heq : periodicCenteredMoment d 2 b n =
      ∑ k ∈ Finset.range (2 * d + 1),
        laguerreWeight d k * ((((n + k : ℕ) : ℚ) + c) ^ 2 * b (n + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.cast_add]
    dsimp [c]
    ring
  have hp := iterated_difference_square_product b c (2 * d - 2) n
  rw [show 2 * d - 2 + 2 = 2 * d by omega,
    show 2 * d - 2 + 1 = 2 * d - 1 by omega] at hp
  rw [Nat.cast_sub (show 2 ≤ 2 * d by omega)] at hp
  push_cast at hp
  have hrel : ((fwdDiff (1 : ℕ))^[2 * d - 1]) b (n + 1) =
      ((fwdDiff (1 : ℕ))^[2 * d - 2]) b (n + 2) -
        ((fwdDiff (1 : ℕ))^[2 * d - 2]) b (n + 1) := by
    rw [show 2 * d - 1 = (2 * d - 2) + 1 by omega, Function.iterate_succ_apply']
    simp only [fwdDiff]
  rw [hrel] at hp
  rw [heq, laguerre_weighted_sequence_sum d n (fun t : ℕ => ((t : ℚ) + c) ^ 2 * b t), hp]
  dsimp [c]
  ring

theorem concrete_exceptional_first_moment (d m n : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (hr : m ∣ n + 2 * d) :
    periodicCenteredMoment d 1 (concretePeriodicSequence d m) n = 0 := by
  rw [periodic_centered_moment_one d n (by omega),
    concrete_periodic_full_difference d m n (by omega) (by omega), if_pos hr,
    concrete_preceding_exceptional_value d m n hd hm hr]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp
  ring

theorem concrete_exceptional_second_moment (d m n : ℕ) (hd : 2 ≤ d) (hm : 2 ≤ m)
    (ho : Odd d) (hr : m ∣ n + 2 * d) :
    periodicCenteredMoment d 2 (concretePeriodicSequence d m) n =
      ((m : ℚ) - 1) / (m : ℚ) *
        (-(d : ℚ) ^ 2 + (d : ℚ) * (2 * (d : ℚ) - 1) * ((m : ℚ) + 1) / 6) := by
  rw [periodic_centered_moment_two d n (by omega),
    concrete_periodic_full_difference d m n (by omega) (by omega), if_pos hr,
    concrete_penultimate_exceptional_value d m n hd hm hr, ho.neg_one_pow]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp
  ring

end PartitionLaguerre

#print axioms PartitionLaguerre.periodic_centered_moment_one
#print axioms PartitionLaguerre.periodic_centered_moment_two
#print axioms PartitionLaguerre.concrete_exceptional_first_moment
#print axioms PartitionLaguerre.concrete_exceptional_second_moment
