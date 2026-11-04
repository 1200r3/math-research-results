import PeriodicDifference

noncomputable section

namespace PartitionLaguerre

theorem difference_sum_range (f : ℕ → ℚ) (m : ℕ) :
    (∑ n ∈ Finset.range m, (f (n + 1) - f n)) = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

theorem difference_preserves_period (f : ℕ → ℚ) (m : ℕ)
    (hp : ∀ n, f (n + m) = f n) :
    ∀ n, fwdDiff (1 : ℕ) f (n + m) = fwdDiff (1 : ℕ) f n := by
  intro n
  unfold fwdDiff
  rw [show n + m + 1 = (n + 1) + m by omega, hp, hp]

theorem iterated_difference_preserves_period (f : ℕ → ℚ) (m h : ℕ)
    (hp : ∀ n, f (n + m) = f n) :
    ∀ n, ((fwdDiff (1 : ℕ))^[h]) f (n + m) = ((fwdDiff (1 : ℕ))^[h]) f n := by
  induction h with
  | zero => exact hp
  | succ h ih =>
    rw [Function.iterate_succ_apply']
    exact difference_preserves_period _ m ih

theorem periodic_difference_zero_mean (f : ℕ → ℚ) (m : ℕ)
    (hp : ∀ n, f (n + m) = f n) :
    (∑ n ∈ Finset.range m, fwdDiff (1 : ℕ) f n) = 0 := by
  change (∑ n ∈ Finset.range m, (f (n + 1) - f n)) = 0
  rw [difference_sum_range]
  have h := hp 0
  simp only [zero_add] at h
  rw [h, sub_self]

theorem periodic_iterated_difference_zero_mean (f : ℕ → ℚ) (m h : ℕ)
    (hp : ∀ n, f (n + m) = f n) :
    (∑ n ∈ Finset.range m, ((fwdDiff (1 : ℕ))^[h + 1]) f n) = 0 := by
  rw [Function.iterate_succ_apply']
  exact periodic_difference_zero_mean _ m (iterated_difference_preserves_period f m h hp)

theorem sum_range_shift_step (f : ℕ → ℚ) (m s : ℕ) :
    (∑ n ∈ Finset.range m, f (n + s + 1)) -
      (∑ n ∈ Finset.range m, f (n + s)) = f (m + s) - f s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [show m + 1 + s = m + s + 1 by omega]
    linarith

theorem periodic_sum_shift (f : ℕ → ℚ) (m s : ℕ)
    (hp : ∀ n, f (n + m) = f n) :
    (∑ n ∈ Finset.range m, f (n + s)) = ∑ n ∈ Finset.range m, f n := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h := sum_range_shift_step f m s
    rw [show m + s = s + m by omega, hp, sub_self] at h
    have he : (∑ n ∈ Finset.range m, f (n + (s + 1))) =
        ∑ n ∈ Finset.range m, f (n + s + 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
    rw [he]
    linarith

theorem iterated_second_difference (f : ℕ → ℚ) (h n : ℕ) :
    ((fwdDiff (1 : ℕ))^[h + 2]) f n =
      ((fwdDiff (1 : ℕ))^[h]) f (n + 2) -
        2 * ((fwdDiff (1 : ℕ))^[h]) f (n + 1) +
          ((fwdDiff (1 : ℕ))^[h]) f n := by
  rw [show h + 2 = (h + 1) + 1 by omega, Function.iterate_succ_apply',
    Function.iterate_succ_apply']
  simp only [fwdDiff]
  rw [show n + 1 + 1 = n + 2 by omega]
  ring

theorem periodic_sequence_constant_of_second_difference (f : ℕ → ℚ) (m : ℕ)
    (hm : 0 < m) (hp : ∀ n, f (n + m) = f n)
    (hsecond : ∀ n, f (n + 2) - 2 * f (n + 1) + f n = 0) :
    ∀ n, f n = f 0 := by
  have hstep : ∀ n, f (n + 1) - f n = f 1 - f 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := hsecond n
      have he : n + 1 + 1 = n + 2 := by omega
      rw [he]
      linarith
  have hlinear : ∀ n, f n = f 0 + (n : ℚ) * (f 1 - f 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep n
      push_cast
      linarith
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hcycle := hp 0
  simp only [zero_add] at hcycle
  rw [hlinear m] at hcycle
  have hmul : (m : ℚ) * (f 1 - f 0) = 0 := by linarith
  have hs : f 1 - f 0 = 0 := (mul_eq_zero.mp hmul).resolve_left hmQ
  intro n
  rw [hlinear n, hs, mul_zero, add_zero]

theorem periodic_second_difference_unique (f g : ℕ → ℚ) (m : ℕ) (hm : 0 < m)
    (hfp : ∀ n, f (n + m) = f n) (hgp : ∀ n, g (n + m) = g n)
    (hsecond : ∀ n, f (n + 2) - 2 * f (n + 1) + f n =
      g (n + 2) - 2 * g (n + 1) + g n)
    (hmean : (∑ n ∈ Finset.range m, f n) = ∑ n ∈ Finset.range m, g n) : f = g := by
  have hc : ∀ n, f n - g n = f 0 - g 0 := by
    apply periodic_sequence_constant_of_second_difference (fun n => f n - g n) m hm
    · intro n
      rw [hfp, hgp]
    · intro n
      have h := hsecond n
      linarith
  have hsum : (∑ n ∈ Finset.range m, (f n - g n)) = 0 := by
    rw [Finset.sum_sub_distrib, hmean, sub_self]
  simp_rw [hc] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hz : f 0 - g 0 = 0 := (mul_eq_zero.mp hsum).resolve_left hmQ
  funext n
  have h := hc n
  linarith

end PartitionLaguerre

#print axioms PartitionLaguerre.difference_sum_range
#print axioms PartitionLaguerre.difference_preserves_period
#print axioms PartitionLaguerre.iterated_difference_preserves_period
#print axioms PartitionLaguerre.periodic_difference_zero_mean
#print axioms PartitionLaguerre.periodic_iterated_difference_zero_mean
#print axioms PartitionLaguerre.sum_range_shift_step
#print axioms PartitionLaguerre.periodic_sum_shift
#print axioms PartitionLaguerre.iterated_second_difference
#print axioms PartitionLaguerre.periodic_sequence_constant_of_second_difference
#print axioms PartitionLaguerre.periodic_second_difference_unique
