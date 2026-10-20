module

public import Erdos940.Cubic.Bridge
public import Erdos940.Progression
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Counting cubic summands in a residue class for Erdős Problem 940

The elementary counting step in Beyer–de Ryke's argument bounds the
progression count using missing values, three-positive-summand values, and
the at-most-two-summand exceptional set.
-/

@[expose] public section

namespace Erdos940

noncomputable def threeProgressionCount (M a N : ℕ) : ℕ := by
  classical
  exact ((progressionBelow M a N).filter ThreePositiveCubeFullSum).card

/-- Every class member is missing, is a three-positive-summand value, or is
covered by the global at-most-two-summand exceptional set. -/
theorem progression_le_missing_add_counts (M a N : ℕ) :
    progressionCount M a N ≤
      missingCount 3 N + threeProgressionCount M a N + atMostTwoCount N := by
  classical
  let P := progressionBelow M a N
  let A := (Finset.range N).filter fun n => ¬ Representable 3 n
  let B := P.filter ThreePositiveCubeFullSum
  let C := (Finset.range N).filter AtMostTwoCubeFullSum
  have hcover : P ⊆ A ∪ (B ∪ C) := by
    intro n hn
    have hnN : n ∈ Finset.range N := (Finset.mem_filter.mp hn).1
    by_cases hr : Representable 3 n
    · rcases (representable_three_iff n).mp hr with hthree | htwo
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hn, hthree⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hnN, htwo⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hnN, hr⟩))
  have hcount : P.card ≤ A.card + B.card + C.card := by
    calc
      P.card ≤ (A ∪ (B ∪ C)).card := Finset.card_le_card hcover
      _ ≤ A.card + (B ∪ C).card := Finset.card_union_le _ _
      _ ≤ A.card + (B.card + C.card) :=
        Nat.add_le_add_left (Finset.card_union_le B C) A.card
      _ = A.card + B.card + C.card := by omega
  simpa only [P, A, B, C, progressionCount, threeProgressionCount,
    missingCount, atMostTwoCount] using hcount

/-- A progression with a small three-summand count gives positive lower
density of missing values once the at-most-two-summand set is sublinear.
The quantitative three-summand estimate is an explicit hypothesis. -/
theorem positiveLowerDensity_of_progression_estimate {M a : ℕ}
    (hM : 0 < M) (ha : a < M)
    (hthree : ∀ᶠ N in Filter.atTop,
      8 * M * threeProgressionCount M a N ≤ N)
    (htwo : SublinearCount atMostTwoCount) :
    HasPositiveLowerDensityComplementFor 3 := by
  have htwo' : ∀ᶠ N in Filter.atTop,
      8 * M * atMostTwoCount N ≤ N :=
    htwo (8 * M) (by positivity)
  have hlarge := eventually_progressionCount_lower hM ha
  refine ⟨8 * M, by positivity, ?_⟩
  filter_upwards [hthree, htwo', hlarge] with N hthreeN htwoN hclass
  have hcover := progression_le_missing_add_counts M a N
  have hscaled :
      8 * M * progressionCount M a N ≤
        8 * M * missingCount 3 N +
        8 * M * threeProgressionCount M a N +
        8 * M * atMostTwoCount N := by
    nlinarith
  nlinarith

end Erdos940
