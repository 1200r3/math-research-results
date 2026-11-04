import TargetStatements
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace PartitionLaguerre

theorem critical_index_large (d : ℕ) (hd : 3 ≤ d) :
    2 * d < criticalIndex d := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : (((2 * d).choose 2 : ℕ) : ℝ) ≤ (Nat.centralBinom d : ℝ) := by
    exact_mod_cast Nat.choose_le_centralBinom 2 d
  rw [Nat.cast_choose_two] at hb
  push_cast at hb
  have heven : 2 ∣ Nat.centralBinom d :=
    Nat.two_dvd_centralBinom_of_one_le (by omega)
  have hdiv : 2 * (Nat.centralBinom d / 2) = Nat.centralBinom d :=
    Nat.mul_div_cancel' heven
  have hmNat : 2 * criticalIndex d = 2 + Nat.centralBinom d := by
    unfold criticalIndex
    omega
  have hm : (2 : ℝ) * (criticalIndex d : ℝ) = 2 + (Nat.centralBinom d : ℝ) := by
    exact_mod_cast hmNat
  have ht : (2 : ℝ) * d < (criticalIndex d : ℝ) := by
    nlinarith [sq_nonneg ((d : ℝ) - 3)]
  exact_mod_cast ht

theorem beta_expression_positive (d m a F C : ℝ)
    (hd : 3 ≤ d) (hm : 2 * d < m)
    (ha : 0 < a) (hF : 0 < F) (hC : 0 < C) :
    0 < betaExpression d m a F C := by
  have hd0 : 0 < d := by linarith
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hd1 : 0 < 2 * d - 1 := by linarith
  have hprod : (2 * d - 1) * (2 * d + 1) < (2 * d - 1) * (m + 1) :=
    mul_lt_mul_of_pos_left (by linarith) hd1
  have hlinear : 6 * d < (2 * d - 1) * (m + 1) := by
    nlinarith [sq_nonneg (d - 3)]
  have hinner : 0 < -d ^ 2 + d * (2 * d - 1) * (m + 1) / 6 := by
    have hp := mul_lt_mul_of_pos_left hlinear hd0
    nlinarith
  have hB2 : 0 < criticalB2 d m := by
    exact mul_pos (div_pos hm1 hm0) hinner
  have hB0 : criticalB0 m < 0 := by
    exact div_neg_of_neg_of_pos (by linarith) hm0
  have hcenter : centeredSecond d m a < 0 := by
    have hp : 0 < a * (2 * d) * (2 * d - 1) * (2 * d + m ^ 2) / 24 := by
      positivity
    unfold centeredSecond
    nlinarith only [hp]
  have hsquare : 0 < m ^ 2 - 4 * d ^ 2 := by
    have hp : 0 < (m - 2 * d) * (m + 2 * d) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hp]
  have hfirst : 0 < a ^ 2 * F * C * d * (m ^ 2 - 4 * d ^ 2) / 12 := by
    positivity
  have hsecond : 0 < 2 * a * (d * (2 * d - 1)) * criticalB2 d m := by
    positivity
  have hthird : 0 < 2 * centeredSecond d m a * criticalB0 m := by
    have hp := mul_pos_of_neg_of_neg hcenter hB0
    nlinarith only [hp]
  unfold betaExpression
  linarith

theorem critical_beta : criticalBetaClaim := by
  intro d hd
  have hmNat := critical_index_large d hd
  have hm0 : 0 < (criticalIndex d : ℝ) := by
    exact_mod_cast (show 0 < criticalIndex d by omega)
  have hF0 : 0 < ((2 * d).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * d)
  unfold criticalBeta
  apply beta_expression_positive
  · exact_mod_cast hd
  · exact_mod_cast hmNat
  · positivity
  · exact hF0
  · exact_mod_cast Nat.centralBinom_pos d

end PartitionLaguerre

#print axioms PartitionLaguerre.critical_index_large
#print axioms PartitionLaguerre.beta_expression_positive
#print axioms PartitionLaguerre.critical_beta
