module

public import Erdos940.Cubic.Bridge
public import Erdos940.Cubic.Parts

/-! Compare the at-most-two-summand count with the paper's positive-summand count. -/

@[expose] public section

namespace Erdos940

/-- An at-most-two-summand value below `N` is either zero or belongs to the
positive one/two-summand set. -/
theorem atMostTwoCount_le_one_add_oneTwoSumsBelow (N : ℕ) :
    atMostTwoCount N ≤ 1 + (oneTwoSumsBelow N).card := by
  classical
  let A := (Finset.range N).filter AtMostTwoCubeFullSum
  have hsubset : A ⊆ insert 0 (oneTwoSumsBelow N) := by
    intro n hn
    obtain ⟨hnN, ⟨a, b, ha, hb, hnSum⟩⟩ := Finset.mem_filter.mp hn
    subst n
    by_cases ha0 : a = 0
    · subst a
      simp only [zero_add] at hnN ⊢
      by_cases hb0 : b = 0
      · subst b
        exact Finset.mem_insert_self _ _
      · have hbN : b < N := Finset.mem_range.mp hnN
        have hbFull : b ∈ cubeFullBelow N := by
          simp [cubeFullBelow, CubeFull, hbN, Nat.pos_of_ne_zero hb0, hb]
        apply Finset.mem_insert_of_mem
        simp only [oneTwoSumsBelow, Finset.mem_union]
        exact Or.inl hbFull
    · by_cases hb0 : b = 0
      · subst b
        simp only [add_zero] at hnN ⊢
        have haN : a < N := Finset.mem_range.mp hnN
        have haFull : a ∈ cubeFullBelow N := by
          simp [cubeFullBelow, CubeFull, haN, Nat.pos_of_ne_zero ha0, ha]
        apply Finset.mem_insert_of_mem
        simp only [oneTwoSumsBelow, Finset.mem_union]
        exact Or.inl haFull
      · have hnN' : a + b < N := Finset.mem_range.mp hnN
        have haN : a < N := by omega
        have hbN : b < N := by omega
        have haFull : a ∈ cubeFullBelow N := by
          simp [cubeFullBelow, CubeFull, haN, Nat.pos_of_ne_zero ha0, ha]
        have hbFull : b ∈ cubeFullBelow N := by
          simp [cubeFullBelow, CubeFull, hbN, Nat.pos_of_ne_zero hb0, hb]
        apply Finset.mem_insert_of_mem
        simp only [oneTwoSumsBelow, Finset.mem_union]
        exact Or.inr (Finset.mem_image₂.mpr ⟨a, haFull, b, hbFull, rfl⟩)
  calc
    atMostTwoCount N = A.card := rfl
    _ ≤ (insert 0 (oneTwoSumsBelow N)).card := Finset.card_le_card hsubset
    _ ≤ (oneTwoSumsBelow N).card + 1 := Finset.card_insert_le _ _
    _ = 1 + (oneTwoSumsBelow N).card := by omega

end Erdos940
