import Erdos940.Quartic.GaussianLBound

/-!
# Summing reciprocal radii over signed Gaussian cells

The outer shell of an integer square of radius `N` has `8N` cells.  Each
noncentral cell in that shell has reciprocal `ℓ∞` radius `1/N`; hence the
sum through radius `N` is at most `8N`.  This is the discrete integral of
the angular-gradient estimate needed for the Gaussian lattice bound.
-/

namespace Erdos940.Quartic.GaussianSignedShell

open Finset Erdos940.Quartic.GaussianLBound

theorem mem_integerBox_iff_natAbs_le (N : ℕ) (p : ℤ × ℤ) :
    p ∈ integerBox N ↔ p.1.natAbs ≤ N ∧ p.2.natAbs ≤ N := by
  change p ∈ (Finset.Icc (-(N : ℤ)) N).product
      (Finset.Icc (-(N : ℤ)) N) ↔ _
  constructor
  · intro hp
    obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hfirst
    obtain ⟨h₃, h₄⟩ := Finset.mem_Icc.mp hsecond
    constructor <;> omega
  · rintro ⟨h₁, h₂⟩
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega

theorem integerBox_mono (N : ℕ) : integerBox N ⊆ integerBox (N + 1) := by
  intro p hp
  rw [mem_integerBox_iff_natAbs_le] at hp ⊢
  omega

theorem max_natAbs_eq_succ_of_shell (N : ℕ) (p : ℤ × ℤ)
    (hp : p ∈ integerBox (N + 1) \ integerBox N) :
    max p.1.natAbs p.2.natAbs = N + 1 := by
  have h := Finset.mem_sdiff.mp hp
  rw [mem_integerBox_iff_natAbs_le] at h
  rw [mem_integerBox_iff_natAbs_le] at h
  omega

noncomputable def reciprocalMax (p : ℤ × ℤ) : ℝ :=
  if max p.1.natAbs p.2.natAbs = 0 then 0
  else (max p.1.natAbs p.2.natAbs : ℝ)⁻¹

noncomputable def reciprocalBoxSum (N : ℕ) : ℝ :=
  ∑ p ∈ integerBox N, reciprocalMax p

theorem reciprocalBoxSum_le_eight_mul (N : ℕ) :
    reciprocalBoxSum N ≤ 8 * N := by
  induction N with
  | zero =>
      simp [reciprocalBoxSum, integerBox, reciprocalMax]
  | succ N ih =>
      have hsubset := integerBox_mono N
      have hsum : reciprocalBoxSum (N + 1) =
          reciprocalBoxSum N +
            ∑ p ∈ integerBox (N + 1) \ integerBox N, reciprocalMax p := by
        simp only [reciprocalBoxSum]
        rw [← Finset.sum_sdiff hsubset]
        ac_rfl
      have hshell : ∀ p ∈ integerBox (N + 1) \ integerBox N,
          reciprocalMax p = ((N + 1 : ℕ) : ℝ)⁻¹ := by
        intro p hp
        have hk := max_natAbs_eq_succ_of_shell N p hp
        have hkreal : (max p.1.natAbs p.2.natAbs : ℝ) = (N + 1 : ℕ) := by
          exact_mod_cast hk
        have hkabs : max |(p.1 : ℝ)| |(p.2 : ℝ)| = (N : ℝ) + 1 := by
          simpa [Nat.cast_add] using hkreal
        simp [reciprocalMax, hk, hkabs]
      have hcard : (integerBox (N + 1) \ integerBox N).card = 8 * (N + 1) := by
        have hdiff := Finset.card_sdiff_add_card_eq_card hsubset
        rw [integerBox_card, integerBox_card] at hdiff
        nlinarith
      rw [hsum]
      calc
        reciprocalBoxSum N +
            ∑ p ∈ integerBox (N + 1) \ integerBox N, reciprocalMax p =
            reciprocalBoxSum N +
              (8 * (N + 1) : ℕ) * ((N + 1 : ℕ) : ℝ)⁻¹ := by
          rw [Finset.sum_congr rfl hshell]
          simp [hcard]
        _ = reciprocalBoxSum N + 8 := by
          have hpos : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
        _ ≤ 8 * ((N + 1 : ℕ) : ℝ) := by
          push_cast
          linarith

end Erdos940.Quartic.GaussianSignedShell
