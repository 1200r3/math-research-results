import ResidueDefinitions

namespace PartitionLaguerre

def residueEvaluationClaim : Prop :=
  ∀ M : ℕ, 0 < M → ∀ F : ℕ → Polynomial ℚ, ∀ j n : ℕ,
    laguerre j (residueSequence M F) n =
      (residueTransform M j F (n % M)).eval (n : ℚ)

def representedSequenceClaim : Prop :=
  ∀ M : ℕ, 0 < M → ∀ F : ℕ → Polynomial ℚ, ∀ f : ℕ → ℚ,
    (∀ n : ℕ, f n = (F (n % M)).eval (n : ℚ)) → ∀ j n : ℕ,
      laguerre j f n = (residueTransform M j F (n % M)).eval (n : ℚ)

def polynomialPositiveBoundClaim : Prop :=
  ∀ P : Polynomial ℚ, 0 < P.leadingCoeff → ∀ x : ℚ,
    (coefficientBound P : ℚ) ≤ x → 0 < P.eval x

def polynomialNegativeBoundClaim : Prop :=
  ∀ P : Polynomial ℚ, P.leadingCoeff < 0 → ∀ x : ℚ,
    (coefficientBound P : ℚ) ≤ x → P.eval x < 0

def uniformResiduePositiveClaim : Prop :=
  ∀ M : ℕ, 0 < M → ∀ d : ℕ, ∀ F : ℕ → Polynomial ℚ,
    (∀ j : ℕ, 1 ≤ j → j ≤ d → ∀ r : ℕ, r < M →
      0 < (residueTransform M j F r).leadingCoeff) →
    ∀ n : ℕ, uniformResidueBound M d F ≤ n →
      ∀ j : ℕ, 1 ≤ j → j ≤ d → 0 < laguerre j (residueSequence M F) n

end PartitionLaguerre
