module

public import Erdos940.Statement
public import Mathlib.Data.Finset.Range
public import Mathlib.Order.Filter.Cofinite

/-!
# Complement density for Erdős Problem 940

For any exponent, positive lower density of the nonrepresentable integers
implies that there are infinitely many of them. The cubic and quartic proofs
establish the needed density bounds in their own folders.
-/

@[expose] public section

namespace Erdos940

/-- Number of nonrepresentable natural numbers below N. -/
noncomputable def missingCount (r N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => ¬ Representable r n).card

/-- A natural-number form of positive lower density for the complement.
The constant C is a reciprocal density bound. -/
def HasPositiveLowerDensityComplementFor (r : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ᶠ N in Filter.atTop, N ≤ C * missingCount r N

/-- If all sufficiently large numbers are representable, the number of
exceptions below any cutoff is bounded. -/
theorem missingCount_bounded_of_eventually_representable {r : ℕ}
    (h : ∀ᶠ n in Filter.atTop, Representable r n) :
    ∃ B : ℕ, ∀ N, missingCount r N ≤ B := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp h
  refine ⟨B, ?_⟩
  intro N
  classical
  unfold missingCount
  calc
    ((Finset.range N).filter fun n => ¬ Representable r n).card
        ≤ (Finset.range B).card := Finset.card_le_card (by
          intro n hn
          have hNot : ¬ Representable r n := (Finset.mem_filter.mp hn).2
          have hnB : n < B := Nat.lt_of_not_ge (fun hBn => hNot (hB n hBn))
          exact Finset.mem_range.mpr hnB)
    _ = B := Finset.card_range B

/-- Positive lower density of the complement rules out eventual representation. -/
theorem coinfiniteFor_of_positiveLowerDensity {r : ℕ}
    (h : HasPositiveLowerDensityComplementFor r) :
    CoinfiniteFor r := by
  intro hFinite
  have hNot : ∀ᶠ n in Filter.atTop,
      n ∉ ({n : ℕ | Representable r n}ᶜ) :=
    Filter.Eventually.filter_mono Filter.atTop_le_cofinite
      hFinite.eventually_cofinite_notMem
  have hEventually : ∀ᶠ n in Filter.atTop, Representable r n :=
    hNot.mono (fun _ hn => not_not.mp hn)
  obtain ⟨B, hB⟩ := missingCount_bounded_of_eventually_representable hEventually
  obtain ⟨C, _hC, hLower⟩ := h
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hLower
  let N := max N₀ (C * B + 1)
  have hBound : N ≤ C * B :=
    (hN₀ N (le_max_left _ _)).trans (Nat.mul_le_mul_left C (hB N))
  have hLarge : C * B < N :=
    (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  exact (Nat.not_le_of_gt hLarge) hBound

end Erdos940
