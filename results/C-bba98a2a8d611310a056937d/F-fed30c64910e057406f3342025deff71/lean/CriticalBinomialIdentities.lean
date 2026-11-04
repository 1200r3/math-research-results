import NextLaguerreMoment

noncomputable section

namespace PartitionLaguerre

theorem critical_next_binomial (d : ℕ) :
    (((2 * d).choose (d + 1) : ℕ) : ℚ) =
      (Nat.centralBinom d : ℚ) * (d : ℚ) / (d + 1 : ℚ) := by
  have h := Nat.choose_succ_right_eq (2 * d) d
  rw [show 2 * d - d = d by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
  have hQ : (((2 * d).choose (d + 1) : ℕ) : ℚ) * (d + 1 : ℚ) =
      (Nat.centralBinom d : ℚ) * (d : ℚ) := by exact_mod_cast h
  exact (eq_div_iff (by positivity)).mpr hQ

theorem critical_previous_central (d : ℕ) (hd : 1 ≤ d) :
    (((2 * d - 2).choose (d - 1) : ℕ) : ℚ) =
      (Nat.centralBinom d : ℚ) * (d : ℚ) / (2 * (2 * (d : ℚ) - 1)) := by
  let A : ℚ := ((2 * d - 2).choose (d - 1) : ℕ)
  let B : ℚ := ((2 * d - 1).choose d : ℕ)
  have h1 := Nat.add_one_mul_choose_eq (2 * d - 2) (d - 1)
  rw [show 2 * d - 2 + 1 = 2 * d - 1 by omega,
    show d - 1 + 1 = d by omega] at h1
  have h2 := Nat.add_one_mul_choose_eq (2 * d - 1) (d - 1)
  rw [show 2 * d - 1 + 1 = 2 * d by omega,
    show d - 1 + 1 = d by omega] at h2
  have hsym : (2 * d - 1).choose (d - 1) = (2 * d - 1).choose d := by
    have h := Nat.choose_symm (show d - 1 ≤ 2 * d - 1 by omega)
    rw [show 2 * d - 1 - (d - 1) = d by omega] at h
    exact h.symm
  rw [hsym, ← Nat.centralBinom_eq_two_mul_choose] at h2
  have h1Q := congrArg (fun n : ℕ => (n : ℚ)) h1
  have h2Q := congrArg (fun n : ℕ => (n : ℚ)) h2
  simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ 2 * d by omega), Nat.cast_one,
    Nat.cast_ofNat] at h1Q
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h2Q
  change (2 * (d : ℚ) - 1) * A = B * (d : ℚ) at h1Q
  change (2 * (d : ℚ)) * B = (Nat.centralBinom d : ℚ) * (d : ℚ) at h2Q
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hB : 2 * B = (Nat.centralBinom d : ℚ) := by
    apply mul_left_cancel₀ hdQ
    calc
      (d : ℚ) * (2 * B) = (2 * (d : ℚ)) * B := by ring
      _ = (Nat.centralBinom d : ℚ) * (d : ℚ) := h2Q
      _ = _ := by ring
  have hscaled : A * (2 * (2 * (d : ℚ) - 1)) = (Nat.centralBinom d : ℚ) * (d : ℚ) := by
    calc
      _ = 2 * ((2 * (d : ℚ) - 1) * A) := by ring
      _ = 2 * (B * (d : ℚ)) := by rw [h1Q]
      _ = (2 * B) * (d : ℚ) := by ring
      _ = _ := by rw [hB]
  have hden : 2 * (2 * (d : ℚ) - 1) ≠ 0 := by
    have h : 1 ≤ (d : ℚ) := by exact_mod_cast hd
    linarith
  exact (eq_div_iff hden).mpr hscaled

theorem critical_binomial_difference (d : ℕ) (hd : 1 ≤ d) :
    (((2 * d - 2).choose d : ℕ) : ℚ) - (((2 * d - 2).choose (d - 1) : ℕ) : ℚ) =
      -(Nat.centralBinom d : ℚ) / (2 * (2 * (d : ℚ) - 1)) := by
  have h := Nat.choose_succ_right_eq (2 * d - 2) (d - 1)
  rw [show d - 1 + 1 = d by omega,
    show 2 * d - 2 - (d - 1) = d - 1 by omega] at h
  have hQ := congrArg (fun n : ℕ => (n : ℚ)) h
  simp only [Nat.cast_mul, Nat.cast_sub hd, Nat.cast_one] at hQ
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have heq : (((2 * d - 2).choose d : ℕ) : ℚ) - (((2 * d - 2).choose (d - 1) : ℕ) : ℚ) =
      -(((2 * d - 2).choose (d - 1) : ℕ) : ℚ) / (d : ℚ) := by
    apply (eq_div_iff hdQ).mpr
    nlinarith [hQ]
  rw [heq, critical_previous_central d hd]
  have hden : 2 * (d : ℚ) - 1 ≠ 0 := by
    have h : 1 ≤ (d : ℚ) := by exact_mod_cast hd
    linarith
  field_simp <;> ring

theorem critical_factorial_next_two (d : ℕ) :
    ((2 * d + 2).factorial : ℚ) =
      (2 * (d : ℚ) + 2) * (2 * (d : ℚ) + 1) * ((2 * d).factorial : ℚ) := by
  rw [show 2 * d + 2 = (2 * d + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

end PartitionLaguerre

#print axioms PartitionLaguerre.critical_next_binomial
#print axioms PartitionLaguerre.critical_previous_central
#print axioms PartitionLaguerre.critical_binomial_difference
#print axioms PartitionLaguerre.critical_factorial_next_two
