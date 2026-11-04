import PolynomialBounds
import LeadingSigns
import CriticalPositivity

namespace PartitionLaguerre

open Polynomial

/-- The exceptional divisibility class has points above every proposed bound. -/
theorem exceptional_class_unbounded (m shift N : ℕ) (hm : 0 < m) :
    ∃ n : ℕ, N ≤ n ∧ m ∣ n + shift := by
  have hmul : N + shift ≤ m * (N + shift) := by
    calc
      N + shift = 1 * (N + shift) := by omega
      _ ≤ m * (N + shift) := Nat.mul_le_mul_right _ (by omega)
  have hshift : shift ≤ m * (N + shift) := by omega
  refine ⟨m * (N + shift) - shift, ?_, ?_⟩
  · omega
  · rw [Nat.sub_add_cancel hshift]
    exact dvd_mul_right m (N + shift)

/-- Strict eventual positivity cannot coexist with eventual negativity on an
unbounded divisibility class. No polynomial representation is assumed here. -/
theorem eventual_positive_excludes_negative_class (d m : ℕ) (f : ℕ → ℚ)
    (hd : 1 ≤ d) (hm : 0 < m)
    (hneg : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m ∣ n + 2 * d → laguerre d f n < 0) :
    ¬ eventualPositiveThrough d f := by
  rintro ⟨Np, hp⟩
  obtain ⟨Nn, hn⟩ := hneg
  obtain ⟨n, hlarge, hdiv⟩ := exceptional_class_unbounded m (2 * d) (max Np Nn) hm
  have hpos := hp n ((le_max_left _ _).trans hlarge) d hd (le_refl d)
  have hnegative := hn n ((le_max_right _ _).trans hlarge) hdiv
  exact (not_lt_of_ge hpos.le) hnegative

/-- Exact arithmetic complement of the admissible parameter region. -/
theorem outside_admissible_iff (d m : ℕ) :
    ¬ (Even d ∨ (Odd d ∧ m ≤ criticalIndex d)) ↔
      Odd d ∧ criticalIndex d < m := by
  rcases Nat.even_or_odd d with he | ho
  · have hno : ¬ Odd d := Nat.not_odd_iff_even.mpr he
    simp [he, hno]
  · have hne : ¬ Even d := Nat.not_even_iff_odd.mpr ho
    simp [hne, ho]

/-- Logical endgame for the main statement. The positive branch and the actual
above-threshold theorem are still explicit proof obligations. -/
theorem main_classification_of_branches
    (hpositive : ∀ d m : ℕ, 2 ≤ d → 2 ≤ m →
      (Even d ∨ (Odd d ∧ m ≤ criticalIndex d)) →
        eventualPositiveThrough d (partitionCount d m))
    (hfailure : aboveThresholdFailure) : mainClassification := by
  intro d m hd hm
  constructor
  · intro hp
    by_contra hout
    obtain ⟨hodd, habove⟩ := (outside_admissible_iff d m).mp hout
    exact eventual_positive_excludes_negative_class d m (partitionCount d m)
      (by omega) (by omega) (hfailure d m hd hm hodd habove) hp
  · exact hpositive d m hd hm

/-- The existing uniform coefficient bound applies to any concretely represented
sequence. The representation and signs remain hypotheses, rather than axioms. -/
theorem eventual_positive_of_residue_model (m d : ℕ) (hm : 0 < m)
    (F : ℕ → ℚ[X]) (f : ℕ → ℚ)
    (hf : ∀ n : ℕ, f n = (F (n % m)).eval (n : ℚ))
    (hLC : ∀ j : ℕ, 1 ≤ j → j ≤ d → ∀ r : ℕ, r < m →
      0 < (residueTransform m j F r).leadingCoeff) :
    eventualPositiveThrough d f := by
  have heq : f = residueSequence m F := funext hf
  rw [heq]
  exact ⟨uniformResidueBound m d F, uniform_residue_positive m hm d F hLC⟩

/-- Explicit eventual negativity from the actual residue-polynomial signs on
the exceptional class. This is the negative counterpart of the existing bound. -/
theorem eventual_negative_of_residue_model (m d : ℕ) (hm : 0 < m) (hd : 1 ≤ d)
    (F : ℕ → ℚ[X]) (f : ℕ → ℚ)
    (hf : ∀ n : ℕ, f n = (F (n % m)).eval (n : ℚ))
    (hLC : ∀ r : ℕ, r < m → m ∣ r + 2 * d →
      (residueTransform m d F r).leadingCoeff < 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m ∣ n + 2 * d → laguerre d f n < 0 := by
  refine ⟨uniformResidueBound m d F, ?_⟩
  intro n hn hdiv
  rw [represented_sequence m hm F f hf d n]
  apply polynomial_negative_bound
  · apply hLC (n % m) (Nat.mod_lt n hm)
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.add_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hdiv
  · have hr : n % m ∈ Finset.range m := Finset.mem_range.mpr (Nat.mod_lt n hm)
    have hj : d ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨hd, le_refl d⟩
    have hb1 : coefficientBound (residueTransform m d F (n % m)) ≤
        (Finset.range m).sup (fun r => coefficientBound (residueTransform m d F r)) :=
      Finset.le_sup (f := fun r => coefficientBound (residueTransform m d F r)) hr
    have hb2 : (Finset.range m).sup (fun r => coefficientBound (residueTransform m d F r)) ≤
        (Finset.Icc 1 d).sup (fun j =>
          (Finset.range m).sup (fun r => coefficientBound (residueTransform m j F r))) :=
      Finset.le_sup (f := fun j =>
        (Finset.range m).sup (fun r => coefficientBound (residueTransform m j F r))) hj
    have hb : coefficientBound (residueTransform m d F (n % m)) ≤ n :=
      hb1.trans (hb2.trans ((le_max_right _ _).trans hn))
    exact_mod_cast hb

/-- A precise remaining obligation for the above-threshold theorem: construct
the specific residue model and prove its actual negative leading coefficients. -/
theorem above_threshold_of_residue_models
    (hmodels : ∀ d m : ℕ, 2 ≤ d → 2 ≤ m → Odd d → criticalIndex d < m →
      ∃ F : ℕ → ℚ[X],
        (∀ n : ℕ, partitionCount d m n = (F (n % m)).eval (n : ℚ)) ∧
        (∀ r : ℕ, r < m → m ∣ r + 2 * d →
          (residueTransform m d F r).leadingCoeff < 0)) :
    aboveThresholdFailure := by
  intro d m hd hm ho habove
  obtain ⟨F, hf, hLC⟩ := hmodels d m hd hm ho habove
  exact eventual_negative_of_residue_model m d (by omega) (by omega)
    F (partitionCount d m) hf hLC

end PartitionLaguerre

#print axioms PartitionLaguerre.exceptional_class_unbounded
#print axioms PartitionLaguerre.eventual_positive_excludes_negative_class
#print axioms PartitionLaguerre.outside_admissible_iff
#print axioms PartitionLaguerre.main_classification_of_branches
#print axioms PartitionLaguerre.eventual_positive_of_residue_model
#print axioms PartitionLaguerre.eventual_negative_of_residue_model
#print axioms PartitionLaguerre.above_threshold_of_residue_models
