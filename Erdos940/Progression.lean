module

public import Erdos940.Density
public import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Linarith

/-!
# Shared residue-class counting for Erdős Problem 940

The elementary size estimates for a residue class are independent of the
exponent. The cubic and quartic proofs apply them to their own representation
counts.
-/

@[expose] public section

namespace Erdos940

/-- Natural numbers below `N` in the class `a (mod M)`. -/
noncomputable def progressionBelow (M a N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun n => n % M = a

noncomputable def progressionCount (M a N : ℕ) : ℕ :=
  (progressionBelow M a N).card

/-- The first `N / M` elements of a residue class occur below `N`, provided
`a` is the standard representative. -/
theorem div_le_progressionCount {M a N : ℕ} (hM : 0 < M) (ha : a < M) :
    N / M ≤ progressionCount M a N := by
  classical
  let f : ℕ → ℕ := fun k => a + M * k
  have hf : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    have h : M * i = M * j := Nat.add_left_cancel hij
    exact (Nat.mul_left_cancel (by omega : 0 < M)) h
  have hsub : (Finset.range (N / M)).image f ⊆ progressionBelow M a N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have hklt : k < N / M := Finset.mem_range.mp hk
    have hmul : M * (k + 1) ≤ N := by
      calc
        M * (k + 1) ≤ M * (N / M) := Nat.mul_le_mul_left M hklt
        _ ≤ N := Nat.mul_div_le N M
    have hlt : a + M * k < N := by
      rw [mul_add] at hmul
      omega
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hlt
    · simp [f, Nat.add_mod, Nat.mod_eq_of_lt ha]
  calc
    N / M = ((Finset.range (N / M)).image f).card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_range]
    _ ≤ (progressionBelow M a N).card := Finset.card_le_card hsub
    _ = progressionCount M a N := rfl

/-- A fixed residue class contains at least `N / (2M)` values below `N`,
expressed without division in the conclusion. -/
theorem eventually_progressionCount_lower {M a : ℕ}
    (hM : 0 < M) (ha : a < M) :
    ∀ᶠ N in Filter.atTop, N ≤ 2 * M * progressionCount M a N := by
  apply Filter.eventually_atTop.mpr
  refine ⟨M, ?_⟩
  intro N hN
  have hdiv : 1 ≤ N / M := (Nat.le_div_iff_mul_le hM).2 (by simpa using hN)
  have hrem : N % M < M := Nat.mod_lt _ hM
  have hdecomp : N % M + M * (N / M) = N := Nat.mod_add_div N M
  have hcount := div_le_progressionCount hM ha (N := N)
  have hfactor : M * (N / M) ≤ M * progressionCount M a N :=
    Nat.mul_le_mul_left M hcount
  have hMle : M ≤ M * (N / M) := by nlinarith
  calc
    N ≤ 2 * (M * (N / M)) := by omega
    _ ≤ 2 * M * progressionCount M a N := by nlinarith

/-- An `o(N)` bound for a counting function, in the elementary form needed
here. -/
def SublinearCount (count : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, 0 < C → ∀ᶠ N in Filter.atTop, C * count N ≤ N

end Erdos940
