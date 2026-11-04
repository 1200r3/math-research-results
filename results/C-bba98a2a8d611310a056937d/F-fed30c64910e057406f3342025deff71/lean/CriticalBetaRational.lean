import CriticalCancellations

noncomputable section

namespace PartitionLaguerre

def betaExpressionQ (d m a F C : ℚ) : ℚ :=
  a ^ 2 * F * C * d * (m ^ 2 - 4 * d ^ 2) / 12 +
    2 * a * (d * (2 * d - 1)) *
      ((m - 1) / m * (-d ^ 2 + d * (2 * d - 1) * (m + 1) / 6)) +
    2 * (-a * (2 * d) * (2 * d - 1) * (2 * d + m ^ 2) / 24) * (-(m - 1) / m)

def criticalBetaQ (d : ℕ) : ℚ :=
  let m : ℚ := criticalIndex d
  let F : ℚ := (2 * d).factorial
  betaExpressionQ d m (1 / (m * F)) F (Nat.centralBinom d)

theorem critical_beta_q_cast (d : ℕ) : (criticalBetaQ d : ℝ) = criticalBeta d := by
  unfold criticalBetaQ criticalBeta betaExpressionQ betaExpression criticalB2 centeredSecond criticalB0
  push_cast <;> ring

theorem critical_beta_q_positive (d : ℕ) (hd : 2 ≤ d) (ho : Odd d) : 0 < criticalBetaQ d := by
  have hd3 : 3 ≤ d := by obtain ⟨k, hk⟩ := ho; omega
  have h := critical_beta d hd3
  rw [← critical_beta_q_cast] at h
  exact_mod_cast h

end PartitionLaguerre

#print axioms PartitionLaguerre.critical_beta_q_cast
#print axioms PartitionLaguerre.critical_beta_q_positive
