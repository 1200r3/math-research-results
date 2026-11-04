import CyclicDifference

noncomputable section

namespace PartitionLaguerre

/-- A discrete Leibniz identity with a linear factor, with the evaluation
shift retained explicitly. -/
theorem iterated_difference_linear_product (b : ℕ → ℚ) (c : ℚ) (q n : ℕ) :
    ((fwdDiff (1 : ℕ))^[q + 1]) (fun t => ((t : ℚ) + c) * b t) n =
      ((n : ℚ) + c) * ((fwdDiff (1 : ℕ))^[q + 1]) b n +
        (q + 1 : ℚ) * ((fwdDiff (1 : ℕ))^[q]) b (n + 1) := by
  induction q generalizing n with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, Function.iterate_zero_apply,
      Nat.cast_zero, zero_add, fwdDiff, Nat.cast_add, Nat.cast_one]
    ring
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    change (((fwdDiff (1 : ℕ))^[q + 1]) (fun t => ((t : ℚ) + c) * b t) (n + 1) -
      ((fwdDiff (1 : ℕ))^[q + 1]) (fun t => ((t : ℚ) + c) * b t) n) = _
    rw [ih (n + 1), ih n]
    simp only [Function.iterate_succ_apply', fwdDiff, Nat.cast_add, Nat.cast_one]
    ring

theorem iterated_difference_square_product (b : ℕ → ℚ) (c : ℚ) (q n : ℕ) :
    ((fwdDiff (1 : ℕ))^[q + 2]) (fun t => ((t : ℚ) + c) ^ 2 * b t) n =
      ((n : ℚ) + c) ^ 2 * ((fwdDiff (1 : ℕ))^[q + 2]) b n +
        (q + 2 : ℚ) * (2 * ((n : ℚ) + c) + 1) *
          ((fwdDiff (1 : ℕ))^[q + 1]) b (n + 1) +
        (q + 2 : ℚ) * (q + 1 : ℚ) * ((fwdDiff (1 : ℕ))^[q]) b (n + 2) := by
  have hfun : (fun t : ℕ => ((t : ℚ) + c) ^ 2 * b t) =
      fun t : ℕ => ((t : ℚ) + c) * (((t : ℚ) + c) * b t) := by
    funext t
    ring
  rw [hfun, show q + 2 = (q + 1) + 1 by omega,
    iterated_difference_linear_product, iterated_difference_linear_product,
    iterated_difference_linear_product]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show n + 1 + 1 = n + 2 by omega]
  ring

end PartitionLaguerre

#print axioms PartitionLaguerre.iterated_difference_linear_product
#print axioms PartitionLaguerre.iterated_difference_square_product
