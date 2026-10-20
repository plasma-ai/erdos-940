import Erdos940.Quartic.CanonicalParts
import Mathlib.Data.Multiset.ZeroCons

/-!
# The four-summand convention

The original statement permits zero and at most four summands. The quartic
first-moment argument counts exactly four positive summands. This file gives
the exact bridge, with sums of at most three as the sparse remainder.
-/

namespace Erdos940.Quartic

def FourPositiveSum (n : ℕ) : Prop :=
  ∃ a b c d : ℕ, FourFull a ∧ FourFull b ∧ FourFull c ∧ FourFull d ∧
    n = a + b + c + d

def AtMostThreeFullSum (n : ℕ) : Prop :=
  ∃ a b c : ℕ, Nat.Full 4 a ∧ Nat.Full 4 b ∧ Nat.Full 4 c ∧
    n = a + b + c

private theorem full_zero : Nat.Full 4 0 := by simp [Nat.Full]

/-- The exact disjunction behind the quartic representation count. -/
theorem representable_four_iff (n : ℕ) :
    Representable 4 n ↔ FourPositiveSum n ∨ AtMostThreeFullSum n := by
  constructor
  · rintro ⟨S, hcard, hfull, hn⟩
    have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨
        S.card = 3 ∨ S.card = 4 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4
    · have hS : S = 0 := Multiset.card_eq_zero.mp h0
      subst S
      right
      refine ⟨0, 0, 0, full_zero, full_zero, full_zero, ?_⟩
      simpa using hn
    · obtain ⟨a, hS⟩ := Multiset.card_eq_one.mp h1
      subst S
      have ha : Nat.Full 4 a := hfull a (by simp)
      right
      refine ⟨a, 0, 0, ha, full_zero, full_zero, ?_⟩
      simpa using hn
    · obtain ⟨a, b, hS⟩ := Multiset.card_eq_two.mp h2
      subst S
      have ha : Nat.Full 4 a := hfull a (by simp)
      have hb : Nat.Full 4 b := hfull b (by simp)
      right
      refine ⟨a, b, 0, ha, hb, full_zero, ?_⟩
      simpa using hn
    · obtain ⟨a, b, c, hS⟩ := Multiset.card_eq_three.mp h3
      subst S
      have ha : Nat.Full 4 a := hfull a (by simp)
      have hb : Nat.Full 4 b := hfull b (by simp)
      have hc : Nat.Full 4 c := hfull c (by simp)
      right
      exact ⟨a, b, c, ha, hb, hc, by simpa [add_assoc] using hn⟩
    · obtain ⟨a, b, c, d, hS⟩ := Multiset.card_eq_four.mp h4
      subst S
      have ha : Nat.Full 4 a := hfull a (by simp)
      have hb : Nat.Full 4 b := hfull b (by simp)
      have hc : Nat.Full 4 c := hfull c (by simp)
      have hd : Nat.Full 4 d := hfull d (by simp)
      by_cases ha0 : a = 0
      · subst a
        right
        exact ⟨b, c, d, hb, hc, hd, by simpa [add_assoc] using hn⟩
      by_cases hb0 : b = 0
      · subst b
        right
        exact ⟨a, c, d, ha, hc, hd, by simpa [add_assoc] using hn⟩
      by_cases hc0 : c = 0
      · subst c
        right
        exact ⟨a, b, d, ha, hb, hd, by simpa [add_assoc] using hn⟩
      by_cases hd0 : d = 0
      · subst d
        right
        exact ⟨a, b, c, ha, hb, hc, by simpa [add_assoc] using hn⟩
      left
      exact ⟨a, b, c, d, ⟨Nat.pos_of_ne_zero ha0, ha⟩,
        ⟨Nat.pos_of_ne_zero hb0, hb⟩, ⟨Nat.pos_of_ne_zero hc0, hc⟩,
        ⟨Nat.pos_of_ne_zero hd0, hd⟩, by simpa [add_assoc] using hn⟩
  · rintro (⟨a, b, c, d, ha, hb, hc, hd, hn⟩ |
      ⟨a, b, c, ha, hb, hc, hn⟩)
    · refine ⟨{a, b, c, d}, ?_, ?_, ?_⟩
      · simp
      · intro s hs
        simp at hs
        rcases hs with rfl | rfl | rfl | rfl <;>
          first | exact ha.2 | exact hb.2 | exact hc.2 | exact hd.2
      · simpa [add_assoc] using hn
    · refine ⟨{a, b, c}, ?_, ?_, ?_⟩
      · simp
      · intro s hs
        simp at hs
        rcases hs with rfl | rfl | rfl <;> assumption
      · simpa [add_assoc] using hn

/-- The values covered by the short-sum case below `N`. -/
noncomputable def atMostThreeCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter AtMostThreeFullSum).card

private theorem short_sum_mem (N a b c : ℕ)
    (ha : Nat.Full 4 a) (hb : Nat.Full 4 b) (hc : Nat.Full 4 c)
    (hN : a + b + c < N) :
    a + b + c ∈ atMostThreeSumsBelow N := by
  classical
  let A := fourFullBelow N
  let B := Finset.image₂ (· + ·) A A
  let C := Finset.image₂ (· + ·) B A
  change a + b + c ∈ insert 0 (A ∪ B ∪ C)
  have hA {x : ℕ} (hx : 0 < x) (hfull : Nat.Full 4 x)
      (hxN : x < N) : x ∈ A := by
    simp [A, fourFullBelow, FourFull, hxN, hx, hfull]
  have hB {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) : x + y ∈ B :=
    Finset.mem_image₂.mpr ⟨x, hx, y, hy, rfl⟩
  have hC {x y z : ℕ} (hxy : x + y ∈ B) (hz : z ∈ A) :
      x + y + z ∈ C :=
    Finset.mem_image₂.mpr ⟨x + y, hxy, z, hz, rfl⟩
  by_cases ha0 : a = 0
  · subst a
    simp only [zero_add] at hN ⊢
    by_cases hb0 : b = 0
    · subst b
      simp only [zero_add] at hN ⊢
      by_cases hc0 : c = 0
      · subst c
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl
            (hA (x := c) (Nat.pos_of_ne_zero hc0) hc (by omega)))))
    · by_cases hc0 : c = 0
      · subst c
        simp only [add_zero] at hN ⊢
        apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl
            (hA (x := b) (Nat.pos_of_ne_zero hb0) hb (by omega)))))
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr
            (hB (hA (x := b) (Nat.pos_of_ne_zero hb0) hb (by omega))
              (hA (x := c) (Nat.pos_of_ne_zero hc0) hc (by omega))))))
  · by_cases hb0 : b = 0
    · subst b
      simp only [add_zero] at hN ⊢
      by_cases hc0 : c = 0
      · subst c
        simp only [add_zero] at hN ⊢
        apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inl
            (hA (x := a) (Nat.pos_of_ne_zero ha0) ha (by omega)))))
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr
            (hB (hA (x := a) (Nat.pos_of_ne_zero ha0) ha (by omega))
              (hA (x := c) (Nat.pos_of_ne_zero hc0) hc (by omega))))))
    · by_cases hc0 : c = 0
      · subst c
        simp only [add_zero] at hN ⊢
        apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_union.mpr (Or.inr
            (hB (hA (x := a) (Nat.pos_of_ne_zero ha0) ha (by omega))
              (hA (x := b) (Nat.pos_of_ne_zero hb0) hb (by omega))))))
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_union.mpr (Or.inr
          (hC (hB (hA (x := a) (Nat.pos_of_ne_zero ha0) ha (by omega))
            (hA (x := b) (Nat.pos_of_ne_zero hb0) hb (by omega)))
            (hA (x := c) (Nat.pos_of_ne_zero hc0) hc (by omega))))

/-- The short-sum count is bounded by the combinatorial sparse set. -/
theorem atMostThreeCount_le (N : ℕ) :
    atMostThreeCount N ≤ (atMostThreeSumsBelow N).card := by
  classical
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnN, a, b, c, ha, hb, hc, hnSum⟩ := Finset.mem_filter.mp hn
  subst n
  exact short_sum_mem N a b c ha hb hc (Finset.mem_range.mp hnN)

theorem atMostThreeCount_eventually_small (C : ℕ) :
    ∀ᶠ N in Filter.atTop, C * atMostThreeCount N ≤ N := by
  filter_upwards [atMostThreeSumsBelow_eventually_small C] with N hN
  exact (Nat.mul_le_mul_left C (atMostThreeCount_le N)).trans hN

end Erdos940.Quartic
