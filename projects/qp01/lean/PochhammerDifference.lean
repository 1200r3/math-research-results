import PeriodicDifference

noncomputable section

namespace PartitionLaguerre

open Polynomial

theorem desc_pochhammer_difference (k : ℕ) :
    fwdDiff (1 : ℚ) (descPochhammer ℚ (k + 1)).eval =
      (k + 1 : ℚ) • (descPochhammer ℚ k).eval := by
  funext x
  have h := congrArg (fun P : ℚ[X] => P.eval (x + 1))
    (descPochhammer_succ_comp_X_sub_one ℚ k)
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_natCast] at h
  rw [show x + 1 - 1 = x by ring] at h
  change (descPochhammer ℚ (k + 1)).eval (x + 1) -
    (descPochhammer ℚ (k + 1)).eval x =
      (k + 1 : ℚ) * (descPochhammer ℚ k).eval x
  linarith

theorem desc_pochhammer_iterated_difference (j q : ℕ) :
    ((fwdDiff (1 : ℚ))^[q]) (descPochhammer ℚ (j + q)).eval =
      (((j + q).factorial : ℚ) / (j.factorial : ℚ)) • (descPochhammer ℚ j).eval := by
  induction q with
  | zero =>
    simp only [Nat.add_zero, Function.iterate_zero_apply]
    rw [div_self (by exact_mod_cast Nat.factorial_ne_zero j), one_smul]
  | succ q ih =>
    have hidx : j + (q + 1) = (j + q) + 1 := by omega
    simp only [hidx]
    rw [Function.iterate_succ_apply, desc_pochhammer_difference (j + q),
      fwdDiff_iter_const_smul, ih, smul_smul]
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] <;> ring

end PartitionLaguerre

#print axioms PartitionLaguerre.desc_pochhammer_difference
#print axioms PartitionLaguerre.desc_pochhammer_iterated_difference
