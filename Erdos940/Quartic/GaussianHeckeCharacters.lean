import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Quartic power-residue characters on Gaussian ideals

We use the fourth cyclotomic field as a model of `ℚ(i)`. The ideal
power-residue symbol provides a multiplicative function on ideals prime to
the parameter and to `2`; its finite-field formula identifies its value at
each prime ideal. A conductor or ray-class modulus is not asserted here.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols

namespace Erdos940.Quartic

abbrev GaussianField := CyclotomicField 4 ℚ

attribute [local instance] Ideal.Quotient.field

noncomputable local instance gaussianPrimeResidueFintype
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    Fintype (𝓞 GaussianField ⧸ P.asIdeal) :=
  Fintype.ofFinite _

private def quarticLevel : ℕ+ := ⟨4, by decide⟩

private theorem gaussianField_primitive_fourth_roots :
    (primitiveRoots 4 GaussianField).Nonempty := by
  letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) ℚ GaussianField
      (Set.mem_singleton 4) (by decide : 4 ≠ 0)
  exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 4)).2 hζ⟩

/-- The ideals at which the quartic power-residue symbol of `R` is defined.
Equivalently, every prime factor avoids the primes over `2R`. -/
def GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
    (I : Ideal (𝓞 GaussianField)) : Prop :=
  I ≠ 0 ∧ ∀ P : HeightOneSpectrum (𝓞 GaussianField),
    P.asIdeal ∣ I →
      (Ideal.absNorm P.asIdeal).Coprime 4 ∧ R ∉ P.asIdeal

/-- Good ideals are closed under multiplication. -/
theorem gaussianQuarticGoodIdeal_mul
    (R : 𝓞 GaussianField) (I J : Ideal (𝓞 GaussianField))
    (hI : GaussianQuarticGoodIdeal R I)
    (hJ : GaussianQuarticGoodIdeal R J) :
    GaussianQuarticGoodIdeal R (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  intro P hP
  rcases P.prime.dvd_mul.mp hP with hPI | hPJ
  · exact hI.2 P hPI
  · exact hJ.2 P hPJ

/-- The quartic Kummer symbol on ideals prime to `2R`. -/
noncomputable def gaussianQuarticIdealSymbol
    (R : 𝓞 GaussianField) (I : Ideal (𝓞 GaussianField))
    (hI : GaussianQuarticGoodIdeal R I) :
    rootsOfUnity (quarticLevel : ℕ) (𝓞 GaussianField) :=
  idealPowerResidueSymbol GaussianField I hI.1 quarticLevel
    gaussianField_primitive_fourth_roots R
    (fun P hP => (hI.2 P hP).1)
    (fun P hP => (hI.2 P hP).2)

/-- The quartic Kummer symbol is multiplicative in its denominator ideal. -/
theorem gaussianQuarticIdealSymbol_mul
    (R : 𝓞 GaussianField) (I J : Ideal (𝓞 GaussianField))
    (hI : GaussianQuarticGoodIdeal R I)
    (hJ : GaussianQuarticGoodIdeal R J) :
    gaussianQuarticIdealSymbol R (I * J)
        (gaussianQuarticGoodIdeal_mul R I J hI hJ) =
      gaussianQuarticIdealSymbol R I hI *
        gaussianQuarticIdealSymbol R J hJ := by
  let hgood : ∀ P : HeightOneSpectrum (𝓞 GaussianField),
      P.asIdeal ∣ I ∨ P.asIdeal ∣ J →
      (Ideal.absNorm P.asIdeal).Coprime 4 ∧ R ∉ P.asIdeal :=
    fun P hP => hP.elim (hI.2 P) (hJ.2 P)
  simpa only [gaussianQuarticIdealSymbol] using
    (idealPowerResidueSymbol_mul_denominator GaussianField I J hI.1 hJ.1
      quarticLevel gaussianField_primitive_fourth_roots R
      (fun P hP => (hgood P hP).1)
      (fun P hP => (hgood P hP).2))

/-- The quartic residue value attached to a prime ideal away from `2R`. -/
noncomputable def gaussianQuarticPrimeSymbol
    (R : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hR : R ∉ P.asIdeal) :
    rootsOfUnity (quarticLevel : ℕ) (𝓞 GaussianField) :=
  primeIdealPowerResidueSymbol GaussianField P quarticLevel
    gaussianField_primitive_fourth_roots h2 R hR

/-- Reduction of a prime-ideal value is the fourth-power residue character
of the finite residue field. This is the local Euler-factor interface. -/
theorem gaussianQuarticPrimeSymbol_reduction
    (R : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hR : R ∉ P.asIdeal) :
    let hn : 4 ∣ Fintype.card (𝓞 GaussianField ⧸ P.asIdeal) - 1 := by
      rw [card_primeIdealResidueField GaussianField P]
      exact dvd_absNorm_sub_one_of_primitiveRoots GaussianField P
        quarticLevel gaussianField_primitive_fourth_roots h2
    rootsOfUnityReductionEquiv GaussianField P quarticLevel
        gaussianField_primitive_fourth_roots h2
        (gaussianQuarticPrimeSymbol R P h2 hR) =
      finiteFieldPowerResidueSymbol
        (𝓞 GaussianField ⧸ P.asIdeal) quarticLevel hn
        (primeIdealResidueUnit GaussianField P R hR) := by
  exact rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol
    GaussianField P quarticLevel gaussianField_primitive_fourth_roots h2 R hR

private theorem gaussianPrimeDivisor_eq
    (P Q : HeightOneSpectrum (𝓞 GaussianField))
    (hQ : Q.asIdeal ∣ P.asIdeal) : Q = P := by
  apply HeightOneSpectrum.asIdeal_injective
  exact (P.isMaximal.eq_of_le Q.isPrime.ne_top
    (Ideal.dvd_iff_le.mp hQ)).symm

/-- A prime ideal away from `2R` belongs to the domain of the ideal symbol. -/
theorem gaussianQuarticGoodIdeal_prime
    (R : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hR : R ∉ P.asIdeal) :
    GaussianQuarticGoodIdeal R P.asIdeal := by
  refine ⟨P.ne_bot, ?_⟩
  intro Q hQ
  have hQP := gaussianPrimeDivisor_eq P Q hQ
  subst Q
  exact ⟨h2, hR⟩

/-- At a prime denominator, the ideal symbol is exactly the prime symbol. -/
theorem gaussianQuarticIdealSymbol_prime
    (R : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hR : R ∉ P.asIdeal) :
    gaussianQuarticIdealSymbol R P.asIdeal
        (gaussianQuarticGoodIdeal_prime R P h2 hR) =
      gaussianQuarticPrimeSymbol R P h2 hR := by
  have hsub : Subsingleton (idealPrimeDivisors GaussianField P.asIdeal) := by
    constructor
    intro Q T
    apply Subtype.ext
    exact (gaussianPrimeDivisor_eq P Q.1 Q.2).trans
      (gaussianPrimeDivisor_eq P T.1 T.2).symm
  letI : Fintype (idealPrimeDivisors GaussianField P.asIdeal) :=
    (idealPrimeDivisors_finite GaussianField P.asIdeal P.ne_bot).fintype
  let Q0 : idealPrimeDivisors GaussianField P.asIdeal := ⟨P, dvd_refl _⟩
  unfold gaussianQuarticIdealSymbol idealPowerResidueSymbol
  rw [Fintype.prod_subsingleton _ Q0]
  have hm : idealPrimeMultiplicity GaussianField P P.asIdeal = 1 := by
    unfold idealPrimeMultiplicity
    exact Associates.count_self P.associates_irreducible
  simp only [Q0, hm, pow_one]
  rfl

/-- A global quartic Kummer ideal character has the expected finite-field
quartic residue value at every admissible prime. -/
theorem gaussianQuarticIdealSymbol_prime_reduction
    (R : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hR : R ∉ P.asIdeal) :
    let hn : 4 ∣ Fintype.card (𝓞 GaussianField ⧸ P.asIdeal) - 1 := by
      rw [card_primeIdealResidueField GaussianField P]
      exact dvd_absNorm_sub_one_of_primitiveRoots GaussianField P
        quarticLevel gaussianField_primitive_fourth_roots h2
    rootsOfUnityReductionEquiv GaussianField P quarticLevel
        gaussianField_primitive_fourth_roots h2
        (gaussianQuarticIdealSymbol R P.asIdeal
          (gaussianQuarticGoodIdeal_prime R P h2 hR)) =
      finiteFieldPowerResidueSymbol
        (𝓞 GaussianField ⧸ P.asIdeal) quarticLevel hn
        (primeIdealResidueUnit GaussianField P R hR) := by
  rw [gaussianQuarticIdealSymbol_prime]
  exact gaussianQuarticPrimeSymbol_reduction R P h2 hR

end Erdos940.Quartic
