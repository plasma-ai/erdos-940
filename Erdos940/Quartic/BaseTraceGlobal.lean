import Erdos940.Quartic.BaseTraceNormalization
import Erdos940.Quartic.CanonicalParts

/-!
# A trace coefficient for every rational prime

This definition uses only the finite-field point count. Its two cases are
identified with a quadratic character at inert primes and the eleven-term
quartic expansion at split primes.
-/

namespace Erdos940.Quartic

noncomputable def quarticBaseTrace
    (d : Fin 4 → CanonicalParts) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    haveI : NeZero p := ⟨hp.ne_zero⟩
    quarticIntrinsicTrace p (fun i => ((d i).val : ZMod p))
  else 0

theorem quarticBaseTrace_eq_intrinsic
    (d : Fin 4 → CanonicalParts) (p : ℕ) (hp : p.Prime) :
    quarticBaseTrace d p =
      letI : NeZero p := ⟨hp.ne_zero⟩
      quarticIntrinsicTrace p (fun i => ((d i).val : ZMod p)) := by
  simp only [quarticBaseTrace, dite_eq_left hp]

theorem quarticBaseTrace_local_density
    (d : Fin 4 → CanonicalParts) (p : ℕ) (hp : p.Prime) :
    (Nat.card {x : Fin 4 → ZMod p //
        ∑ i, ((d i).val : ZMod p) * x i ^ 4 = 0} : ℝ) /
          (p : ℝ) ^ 3 =
      1 + quarticBaseTrace d p *
        ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [quarticBaseTrace_eq_intrinsic d p hp]
  exact quarticIntrinsicTrace_local_density p hp.one_lt _

theorem quarticBaseTrace_abs_le_one_of_inert
    (d : Fin 4 → CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hmod : p % 4 = 3)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    |quarticBaseTrace d p| ≤ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [quarticBaseTrace_eq_intrinsic d p hp]
  exact quarticIntrinsicTrace_abs_le_one_of_inert p hmod _ hunit

theorem quarticBaseTrace_abs_le_21_of_quartic_character
    (d : Fin 4 → CanonicalParts) (p : ℕ)
    (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    |quarticBaseTrace d p| ≤ 21 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [quarticBaseTrace_eq_intrinsic d p hp]
  exact quarticIntrinsicTrace_abs_le_21_of_quartic_character
    p χ hχ ψ hψ _ hunit

theorem quarticBaseTrace_eq_eleven_real_characters
    (d : Fin 4 → CanonicalParts) (p : ℕ) [Fact p.Prime]
    (hp : p.Prime) (χ : MulChar (ZMod p) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0)
    (π : GaussianInt) (hJ : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2) :
    quarticBaseTrace d p =
      ∑ k : Fin 11,
        (quarticElevenCharacterConstituent p χ
          (fun i => ((d i).val : ZMod p)) π k).re := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [quarticBaseTrace_eq_intrinsic d p hp]
  exact quarticIntrinsicTrace_eq_eleven_real_characters
    p χ hχ ψ hψ _ hunit π hJ

end Erdos940.Quartic
