module

public import Erdos940.Density
public import Mathlib.Data.Finset.Card

/-!
# The cubic summand conventions in Erdős Problem 940

Beyer–de Ryke count sums of exactly three *positive* cube-full integers. The
problem statement allows at most three natural summands, including zero. This
file separates a representation into an exactly-three-positive part and a
remaining part with at most two summands. The latter is the sparse exceptional
set in the paper's proof of Corollary 1.2.
-/

@[expose] public section

namespace Erdos940

/-- A sum in the paper's set `ℱ + ℱ + ℱ`. -/
def ThreePositiveCubeFullSum (n : ℕ) : Prop :=
  ∃ a b c : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧
    Nat.Full 3 a ∧ Nat.Full 3 b ∧ Nat.Full 3 c ∧
    n = a + b + c

/-- A sum of at most two cube-full integers. Zero summands are permitted, so
this includes the empty and one-summand cases. -/
def AtMostTwoCubeFullSum (n : ℕ) : Prop :=
  ∃ a b : ℕ, Nat.Full 3 a ∧ Nat.Full 3 b ∧ n = a + b

private theorem full_zero : Nat.Full 3 0 := by
  simp [Nat.Full]

/-- The paper's three-positive-summand set together with its sparse
one- and two-summand exception is exactly the set in the Lean statement. -/
theorem representable_three_iff (n : ℕ) :
    Representable 3 n ↔
      ThreePositiveCubeFullSum n ∨ AtMostTwoCubeFullSum n := by
  constructor
  · rintro ⟨S, hcard, hfull, hn⟩
    have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · have hS : S = 0 := Multiset.card_eq_zero.mp h0
      subst S
      right
      refine ⟨0, 0, full_zero, full_zero, ?_⟩
      simpa using hn
    · obtain ⟨a, hS⟩ := Multiset.card_eq_one.mp h1
      subst S
      have ha : Nat.Full 3 a := hfull a (by simp)
      right
      refine ⟨a, 0, ha, full_zero, ?_⟩
      simpa using hn
    · obtain ⟨a, b, hS⟩ := Multiset.card_eq_two.mp h2
      subst S
      have ha : Nat.Full 3 a := hfull a (by simp)
      have hb : Nat.Full 3 b := hfull b (by simp)
      right
      exact ⟨a, b, ha, hb, by simpa using hn⟩
    · obtain ⟨a, b, c, hS⟩ := Multiset.card_eq_three.mp h3
      subst S
      have ha : Nat.Full 3 a := hfull a (by simp)
      have hb : Nat.Full 3 b := hfull b (by simp)
      have hc : Nat.Full 3 c := hfull c (by simp)
      by_cases ha0 : a = 0
      · subst a
        right
        exact ⟨b, c, hb, hc, by simpa [add_assoc] using hn⟩
      by_cases hb0 : b = 0
      · subst b
        right
        exact ⟨a, c, ha, hc, by simpa [add_assoc] using hn⟩
      by_cases hc0 : c = 0
      · subst c
        right
        exact ⟨a, b, ha, hb, by simpa [add_assoc] using hn⟩
      left
      exact ⟨a, b, c, Nat.pos_of_ne_zero ha0, Nat.pos_of_ne_zero hb0,
        Nat.pos_of_ne_zero hc0, ha, hb, hc, by simpa [add_assoc] using hn⟩
  · rintro (⟨a, b, c, _ha0, _hb0, _hc0, ha, hb, hc, hn⟩ |
      ⟨a, b, ha, hb, hn⟩)
    · refine ⟨{a, b, c}, ?_, ?_, ?_⟩
      · simp
      · intro s hs
        simp at hs
        rcases hs with rfl | rfl | rfl <;> assumption
      · simpa [add_assoc] using hn
    · refine ⟨{a, b}, ?_, ?_, ?_⟩
      · simp
      · intro s hs
        simp at hs
        rcases hs with rfl | rfl <;> assumption
      · simpa using hn

/-- A missing value of the paper's three-term set is missing from the Erdős
representation set whenever it also avoids the at-most-two-summand set. -/
theorem not_representable_three_of_missing_both {n : ℕ}
    (hthree : ¬ ThreePositiveCubeFullSum n)
    (htwo : ¬ AtMostTwoCubeFullSum n) :
    ¬ Representable 3 n := by
  intro h
  rcases (representable_three_iff n).mp h with h | h
  · exact hthree h
  · exact htwo h

/-- The number of paper-style three-term sums below `N`. -/
noncomputable def threePositiveCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter ThreePositiveCubeFullSum).card

/-- The number of values below `N` covered by at most two summands. -/
noncomputable def atMostTwoCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter AtMostTwoCubeFullSum).card

/-- Finite counting form of the last step in Beyer–de Ryke's Corollary 1.2.
It leaves the two analytic estimates as separate tasks: the paper bounds the
three-term set away from full density and bounds the two-term set by `o(N)`. -/
theorem range_le_missing_add_counts (N : ℕ) :
    N ≤ missingCount 3 N + threePositiveCount N + atMostTwoCount N := by
  classical
  let A := (Finset.range N).filter fun n => ¬ Representable 3 n
  let B := (Finset.range N).filter ThreePositiveCubeFullSum
  let C := (Finset.range N).filter AtMostTwoCubeFullSum
  have hcover : Finset.range N ⊆ A ∪ (B ∪ C) := by
    intro n hn
    by_cases hr : Representable 3 n
    · rcases (representable_three_iff n).mp hr with hthree | htwo
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hn, hthree⟩))))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hn, htwo⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hn, hr⟩))
  have hcount : N ≤ A.card + B.card + C.card := by
    calc
      N = (Finset.range N).card := (Finset.card_range N).symm
      _ ≤ (A ∪ (B ∪ C)).card := Finset.card_le_card hcover
      _ ≤ A.card + (B ∪ C).card := Finset.card_union_le _ _
      _ ≤ A.card + (B.card + C.card) :=
        Nat.add_le_add_left (Finset.card_union_le B C) A.card
      _ = A.card + B.card + C.card := by omega
  simpa only [A, B, C, missingCount, threePositiveCount, atMostTwoCount] using hcount

end Erdos940
