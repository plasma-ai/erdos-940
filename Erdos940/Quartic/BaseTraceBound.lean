import Erdos940.Quartic.BaseTraceGlobal
import Erdos940.Quartic.GaussianSplitPrimeExistence
import Erdos940.Quartic.JacobiGaussianGenerator
import Mathlib.NumberTheory.LegendreSymbol.Complex

/-!
# Uniform bound for the intrinsic base-prime trace

At inert primes this is a quadratic character. At split primes a Gaussian
prime and a quartic residue character supply 21 unit-size Gauss terms.
-/

namespace Erdos940.Quartic

theorem quarticBaseTrace_abs_le_21
    (d : Fin 4 → CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hodd : 2 < p)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    |quarticBaseTrace d p| ≤ 21 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hpodd with ⟨k, hk⟩
    omega
  rcases hmod with hsplit | hinert
  · obtain ⟨π, hπnorm, hπre, hπim⟩ :=
      exists_normalized_gaussian_prime p hsplit
    obtain ⟨χ, hχ, _⟩ := exists_quartic_character_jacobi_square_at_prime
      p hsplit π hπnorm hπre hπim
    let ψ : AddChar (ZMod p) ℂ :=
      AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
    have hψ : ψ.IsPrimitive :=
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
    exact quarticBaseTrace_abs_le_21_of_quartic_character
      d p hp χ hχ ψ hψ hunit
  · exact (quarticBaseTrace_abs_le_one_of_inert d p hp hinert hunit).trans (by norm_num)

end Erdos940.Quartic
