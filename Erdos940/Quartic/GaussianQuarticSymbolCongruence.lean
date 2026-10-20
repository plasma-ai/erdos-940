import Erdos940.Quartic.GaussianFiniteConstituentTrace
import Erdos940.Quartic.GaussianHeckeCharacters

/-!
# Congruence invariance of the Gaussian quartic prime symbol

Two rational numerators congruent modulo a rational prime have the same
quartic symbol at every Gaussian prime ideal above it.
-/

namespace Erdos940.Quartic.GaussianQuarticSymbolCongruence

open scoped NumberField
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open Erdos940.Quartic

theorem integer_cast_eq_mod_prime_ideal
    (p : ℕ) (R T : ℤ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hnorm : Ideal.absNorm P.asIdeal = p)
    (hmod : (R : ZMod p) = (T : ZMod p)) :
    ((R : 𝓞 GaussianField) : 𝓞 GaussianField ⧸ P.asIdeal) =
      ((T : 𝓞 GaussianField) : 𝓞 GaussianField ⧸ P.asIdeal) := by
  have hdiv : (p : ℤ) ∣ R - T :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub T R p).mp hmod.symm
  obtain ⟨k, hk⟩ := hdiv
  have hp : (p : 𝓞 GaussianField) ∈ P.asIdeal := by
    rw [← hnorm]
    exact Ideal.absNorm_mem P.asIdeal
  apply Ideal.Quotient.eq.mpr
  have hcast : (R : 𝓞 GaussianField) - (T : 𝓞 GaussianField) =
      (p : 𝓞 GaussianField) * (k : 𝓞 GaussianField) := by
    exact_mod_cast hk
  rw [hcast]
  exact P.asIdeal.mul_mem_right _ hp

theorem gaussianQuarticPrimeSymbol_int_congr
    (p : ℕ) (R T : ℤ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hnorm : Ideal.absNorm P.asIdeal = p)
    (hmod : (R : ZMod p) = (T : ZMod p))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hR : (R : 𝓞 GaussianField) ∉ P.asIdeal)
    (hT : (T : 𝓞 GaussianField) ∉ P.asIdeal) :
    gaussianQuarticPrimeSymbol (R : 𝓞 GaussianField) P h2 hR =
      gaussianQuarticPrimeSymbol (T : 𝓞 GaussianField) P h2 hT := by
  have hq := integer_cast_eq_mod_prime_ideal p R T P hnorm hmod
  have hu : primeIdealResidueUnit GaussianField P (R : 𝓞 GaussianField) hR =
      primeIdealResidueUnit GaussianField P (T : 𝓞 GaussianField) hT := by
    apply Units.ext
    exact hq
  unfold gaussianQuarticPrimeSymbol primeIdealPowerResidueSymbol
  rw [hu]

end Erdos940.Quartic.GaussianQuarticSymbolCongruence
