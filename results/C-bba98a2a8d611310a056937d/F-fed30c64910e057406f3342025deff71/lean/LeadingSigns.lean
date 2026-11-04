import TargetStatements
import Lean.Elab.Tactic.Omega

namespace PartitionLaguerre

/-- The two leading numerators have the prescribed signs exactly in the
parameter range appearing in the classification statement. -/
theorem leading_signs : leadingSignsClaim := by
  intro d m hd hm
  have hcentral : 2 < Nat.centralBinom d := by
    have h := Nat.centralBinom_strictMono (show 1 < d by omega)
    simpa only [show Nat.centralBinom 1 = 2 by rfl] using h
  obtain h_even | h_odd := Nat.even_or_odd d
  · simp [leadingNumerator, h_even.neg_one_pow, h_even] <;> omega
  · have h_not_even : ¬ Even d := Nat.not_even_iff_odd.mpr h_odd
    simp [leadingNumerator, criticalIndex, h_odd.neg_one_pow, h_odd,
      h_not_even] <;> omega

end PartitionLaguerre

#print axioms PartitionLaguerre.leading_signs
