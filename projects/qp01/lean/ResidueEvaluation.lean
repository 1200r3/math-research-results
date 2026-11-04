import ResidueTargets

namespace PartitionLaguerre

theorem residue_evaluation : residueEvaluationClaim := by
  intro M hM F j n
  unfold laguerre residueTransform
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, residueSequence,
    Nat.mod_add_mod, Nat.cast_add]

theorem represented_sequence : representedSequenceClaim := by
  intro M hM F f hf j n
  have hfun : f = residueSequence M F := funext hf
  rw [hfun]
  exact residue_evaluation M hM F j n

end PartitionLaguerre

#print axioms PartitionLaguerre.residue_evaluation
#print axioms PartitionLaguerre.represented_sequence
