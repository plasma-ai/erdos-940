import Erdos940.Quartic.GlobalElevenCharacter
import Erdos940.Quartic.GaussianCMCharacter
import Erdos940.Quartic.GaussianEtaPrimeSum
import Erdos940.Quartic.GaussianFiniteConstituentTrace
import Erdos940.Quartic.GaussianPrimeSumTransfer

/-!
# The CM constituent in the eleven-term rational-prime trace

The tenth constituent is the sum of the infinity-type-two ideal character
over the two Gaussian primes above each split rational prime.
-/

namespace Erdos940.Quartic.GaussianCMConstituentBridge

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianCMCharacter
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianEtaPrimeSum

/-- The complex embedding compatible with the standard copy of `ℤ[i]`. -/
noncomputable def gaussianCanonicalFieldEmbedding : GaussianField →+* ℂ :=
  IsFractionRing.lift fourthIntegerRingToComplex_injective

theorem gaussianCanonicalFieldEmbedding_gaussian (z : GaussianInt) :
    gaussianCanonicalFieldEmbedding
      ((gaussianFourthIntegerRingEquiv z : 𝓞 GaussianField) : GaussianField) =
        (z : ℂ) := by
  rw [gaussianCanonicalFieldEmbedding, IsFractionRing.lift_algebraMap]
  exact fourthIntegerRingToComplex_gaussian z

theorem gaussianQuarticComplexValue_canonical
    (ζ : rootsOfUnity 4 (𝓞 GaussianField)) :
    gaussianQuarticComplexValue gaussianCanonicalFieldEmbedding ζ =
      fourthIntegerRingToComplex
        ((((ζ : (𝓞 GaussianField)ˣ) : 𝓞 GaussianField))) := by
  unfold gaussianQuarticComplexValue
  exact IsFractionRing.lift_algebraMap
    fourthIntegerRingToComplex_injective _

/-- The global ideal symbol evaluated at the selected split Gaussian prime
agrees with the oriented finite-field quartic character. -/
theorem quarticIdealWeight_selected_prime_eq_character
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (z : GaussianInt) (hz : ρ z ≠ 0) :
    quarticIdealWeight (gaussianFourthIntegerRingEquiv z)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ).asIdeal =
        χ (ρ z) := by
  let P := gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ
  have h2 := gaussianPrimeIdealOfReduction_coprime_four
    q hqmod ρ π hπ0 hρπ
  have hR := gaussianPrimeIdealOfReduction_not_mem
    q ρ π hπ0 hρπ z hz
  have hgood := gaussianQuarticGoodIdeal_prime
    (gaussianFourthIntegerRingEquiv z) P h2 hR
  rw [quarticIdealWeight, dif_pos hgood,
    gaussianQuarticIdealSymbol_prime]
  unfold gaussianQuarticComplexValue
  rw [gaussianCanonicalFieldEmbedding, IsFractionRing.lift_algebraMap]
  exact gaussianQuarticPrimeSymbol_complex_eq_character
    q hqmod ρ π hπ0 hρπ χ hχ hρchar z hz h2 hR

theorem quarticIdealWeight_zero_of_reduction_zero
    (q : ℕ) [Fact q.Prime]
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (z : GaussianInt) (hz : ρ z = 0) :
    quarticIdealWeight (gaussianFourthIntegerRingEquiv z)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ).asIdeal = 0 := by
  let P := gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ
  have hmem : gaussianFourthIntegerRingEquiv z ∈ P.asIdeal := by
    change gaussianFourthIntegerRingEquiv z ∈
      RingHom.ker (fourthIntegerRingReduction q ρ)
    simpa [RingHom.mem_ker] using hz
  have hbad : ¬ GaussianQuarticGoodIdeal
      (gaussianFourthIntegerRingEquiv z) P.asIdeal := by
    intro hgood
    exact (hgood.2 P (dvd_refl _)).2 hmem
  change quarticIdealWeight (gaussianFourthIntegerRingEquiv z)
    gaussianCanonicalFieldEmbedding P.asIdeal = 0
  simp [quarticIdealWeight, hbad]

/-- At a parity-normalized prime of rational norm `q`, the algebraic part
of the CM character is exactly the angular numerator in Eq. (5). -/
theorem gaussianNuIdealWeight_normalized_prime
    (q : ℕ) (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) :
    gaussianNuIdealWeight (gaussianPrincipalIdeal π) =
      (π : ℂ) ^ 2 / (q : ℂ) := by
  have hnormalized : GaussianParityNormalized π := ⟨hπre, hπim⟩
  have hodd := gaussianPrincipalIdeal_odd_of_normalized π hnormalized
  rw [gaussianNuIdealWeight_of_odd _ hodd,
    ← map_pow,
    normalizedGaussianIdealGenerator_sq_eq
      (gaussianPrincipalIdeal π) hodd π rfl hnormalized,
    map_pow, absNorm_gaussianPrincipalIdeal]
  simp [hπnorm]

theorem gaussianNuIdealWeight_conjugate_prime
    (q : ℕ) (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) :
    gaussianNuIdealWeight (gaussianPrincipalIdeal (star π)) =
      star (π : ℂ) ^ 2 / (q : ℂ) := by
  have hstarNorm : (star π).norm = q := by
    rw [Zsqrtd.norm_conj, hπnorm]
  have hstarRe : ((star π).re : ZMod 2) = 1 := by
    simpa using hπre
  have hstarIm : ((star π).im : ZMod 2) = 0 := by
    simpa using hπim
  rw [gaussianNuIdealWeight_normalized_prime q (star π)
    hstarNorm hstarRe hstarIm, GaussianInt.toComplex_star]
  rfl

theorem quarticIdealWeight_selected_prime_rational
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (D : ℕ) (hD : (D : ZMod q) ≠ 0) :
    quarticIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ).asIdeal =
        χ (D : ZMod q) := by
  have hρD : ρ (D : GaussianInt) = (D : ZMod q) := by simp
  have hR : (D : 𝓞 GaussianField) =
      gaussianFourthIntegerRingEquiv (D : GaussianInt) := by simp
  rw [hR]
  simpa only [hρD] using
    quarticIdealWeight_selected_prime_eq_character q hqmod ρ π hπ0 hρπ
      χ hχ hρchar (D : GaussianInt) (hρD ▸ hD)

theorem quarticIdealWeight_conjugate_prime_rational
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (D : ℕ) (hD : (D : ZMod q) ≠ 0) :
    quarticIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π hπ0)
        (conjugateGaussianReduction_star_prime q ρ π hρπ)).asIdeal =
        (χ (D : ZMod q))⁻¹ := by
  have hχinv : orderOf χ⁻¹ = 4 := by
    simpa [hχ] using (orderOf_inv χ)
  have hρcharbar :=
    conjugateReduction_matches_inverse_character q ρ χ hχ hρchar
  have h := quarticIdealWeight_selected_prime_rational q hqmod
    (conjugateGaussianReduction q ρ) (star π)
    (conjugate_gaussian_prime_ne_zero π hπ0)
    (conjugateGaussianReduction_star_prime q ρ π hρπ)
    χ⁻¹ hχinv hρcharbar D hD
  simpa only [MulChar.inv_apply_eq_inv'] using h

theorem gaussianEta_selected_prime_zero_of_divides
    (q : ℕ) [Fact q.Prime]
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (D : ℕ) (hD : (D : ZMod q) = 0) :
    gaussianEtaIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ).asIdeal = 0 := by
  have hρD : ρ (D : GaussianInt) = 0 := by simpa using hD
  have hR : (D : 𝓞 GaussianField) =
      gaussianFourthIntegerRingEquiv (D : GaussianInt) := by simp
  have hψ := quarticIdealWeight_zero_of_reduction_zero
    q ρ π hπ0 hρπ (D : GaussianInt) hρD
  rw [gaussianEtaIdealWeight, hR, hψ]
  simp

theorem gaussianEta_conjugate_prime_zero_of_divides
    (q : ℕ) [Fact q.Prime]
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (D : ℕ) (hD : (D : ZMod q) = 0) :
    gaussianEtaIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π hπ0)
        (conjugateGaussianReduction_star_prime q ρ π hρπ)).asIdeal = 0 := by
  have hρD : conjugateGaussianReduction q ρ (D : GaussianInt) = 0 := by
    simpa [conjugateGaussianReduction, starRingEnd_apply] using hD
  have hR : (D : 𝓞 GaussianField) =
      gaussianFourthIntegerRingEquiv (D : GaussianInt) := by simp
  have hψ := quarticIdealWeight_zero_of_reduction_zero q
    (conjugateGaussianReduction q ρ) (star π)
    (conjugate_gaussian_prime_ne_zero π hπ0)
    (conjugateGaussianReduction_star_prime q ρ π hρπ)
    (D : GaussianInt) hρD
  rw [gaussianEtaIdealWeight, hR, hψ]
  simp

theorem gaussianEta_selected_prime_eq_CM_term
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (D : ℕ) (hD : (D : ZMod q) ≠ 0) :
    gaussianEtaIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π))).asIdeal =
      (χ (D : ZMod q))⁻¹ * ((π : ℂ) ^ 2 / (q : ℂ)) := by
  let hπ0 := gaussianPrime_ne_zero_of_norm q π hπnorm
  let hρπ := (hker π).2 (dvd_refl π)
  have hP := gaussianPrimeIdealOfReduction_eq_span
    q ρ π hπ0 hρπ hker
  have hψ : quarticIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding (gaussianPrincipalIdeal π) =
        χ (D : ZMod q) := by
    change quarticIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (Ideal.span {gaussianFourthIntegerRingEquiv π}) = _
    rw [← hP]
    exact quarticIdealWeight_selected_prime_rational q hqmod ρ π hπ0 hρπ
      χ hχ hρchar D hD
  rw [gaussianEtaIdealWeight, hP]
  change gaussianNuIdealWeight (gaussianPrincipalIdeal π) *
      (quarticIdealWeight (D : 𝓞 GaussianField)
        gaussianCanonicalFieldEmbedding (gaussianPrincipalIdeal π))⁻¹ = _
  rw [gaussianNuIdealWeight_normalized_prime q π hπnorm hπre hπim,
    hψ]
  ring

theorem gaussianEta_conjugate_prime_eq_CM_term
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (D : ℕ) (hD : (D : ZMod q) ≠ 0) :
    gaussianEtaIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π
          (gaussianPrime_ne_zero_of_norm q π hπnorm))
        (conjugateGaussianReduction_star_prime q ρ π
          ((hker π).2 (dvd_refl π)))).asIdeal =
      χ (D : ZMod q) * (star (π : ℂ) ^ 2 / (q : ℂ)) := by
  let hπ0 := gaussianPrime_ne_zero_of_norm q π hπnorm
  let hρπ := (hker π).2 (dvd_refl π)
  have hPbar := conjugateGaussianPrimeIdeal_eq_span
    q ρ π hπ0 hρπ hker
  have hψ : quarticIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrincipalIdeal (star π)) =
        (χ (D : ZMod q))⁻¹ := by
    change quarticIdealWeight (D : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (Ideal.span {gaussianFourthIntegerRingEquiv (star π)}) = _
    rw [← hPbar]
    exact quarticIdealWeight_conjugate_prime_rational q hqmod ρ π
      hπ0 hρπ χ hχ hρchar D hD
  rw [gaussianEtaIdealWeight, hPbar]
  change gaussianNuIdealWeight (gaussianPrincipalIdeal (star π)) *
      (quarticIdealWeight (D : 𝓞 GaussianField)
        gaussianCanonicalFieldEmbedding
        (gaussianPrincipalIdeal (star π)))⁻¹ = _
  rw [gaussianNuIdealWeight_conjugate_prime q π hπnorm hπre hπim,
    hψ, inv_inv]
  ring

/-- The full norm-`q` Gaussian prime fiber is the two-term CM trace. -/
theorem quarticCMCharacterTrace_eq_eta_norm_fiber_sum
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q)
    (D : ℕ) (hD : (D : ZMod q) ≠ 0)
    (hDa : (D : ZMod q) = ∏ i, a i) :
    quarticCMCharacterTrace q χ a π =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        gaussianEtaIdealWeight (D : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal := by
  classical
  have hne := conjugateGaussianPrimeIdeal_ne
    q ρ π hπnorm hπre hπim hker
  rw [gaussianSplitNormPrimeFiber, Finset.sum_pair hne]
  rw [gaussianEta_selected_prime_eq_CM_term q hqmod ρ π
    hπnorm hπre hπim hker χ hχ hρchar D hD,
    gaussianEta_conjugate_prime_eq_CM_term q hqmod ρ π
      hπnorm hπre hπim hker χ hχ hρchar D hD]
  simp only [quarticCMCharacterTrace, ← hDa, MulChar.inv_apply_eq_inv']

/-- The fiber identity remains valid at coefficient-bad split primes: both
ideal-symbol weights and the finite-field CM trace then vanish. -/
theorem quarticCMCharacterTrace_eq_eta_norm_fiber_sum_all
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q)
    (D : ℕ) (hDa : (D : ZMod q) = ∏ i, a i) :
    quarticCMCharacterTrace q χ a π =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        gaussianEtaIdealWeight (D : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal := by
  by_cases hD : (D : ZMod q) = 0
  · classical
    have hne := conjugateGaussianPrimeIdeal_ne
      q ρ π hπnorm hπre hπim hker
    rw [gaussianSplitNormPrimeFiber, Finset.sum_pair hne]
    rw [gaussianEta_selected_prime_zero_of_divides q ρ π
      (gaussianPrime_ne_zero_of_norm q π hπnorm)
      ((hker π).2 (dvd_refl π)) D hD,
      gaussianEta_conjugate_prime_zero_of_divides q ρ π
      (gaussianPrime_ne_zero_of_norm q π hπnorm)
      ((hker π).2 (dvd_refl π)) D hD]
    have hprod : ∏ i, a i = 0 := hDa.symm.trans hD
    simp [quarticCMCharacterTrace, hprod, MulChar.map_zero]
  · exact quarticCMCharacterTrace_eq_eta_norm_fiber_sum
      q hqmod ρ π hπnorm hπre hπim hker χ hχ hρchar a D hD hDa

/-- At each good split rational prime, the global `j=10` constituent is
the real trace of the CM ideal character over the two-prime norm fiber. -/
theorem baseConstituent_ten_split_eq_eta_norm_fiber
    (d : Fin 4 → CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hsplit : p % 4 = 1)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    baseConstituent d (10 : Fin 11) p =
      letI : Fact p.Prime := ⟨hp⟩
      let s := quarticSplitPrimeChoice p hsplit
      (∑ Q ∈ gaussianSplitNormPrimeFiber p s.ρ s.π s.norm_eq s.kernel_eq,
        gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal).re := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := quarticSplitPrimeChoice p hsplit
  have hDa : (coefficientProduct d : ZMod p) =
      ∏ i, ((d i).val : ZMod p) := by
    simp [coefficientProduct]
  have hD : (coefficientProduct d : ZMod p) ≠ 0 := by
    rw [hDa]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hunit i)
  rw [baseConstituent_split d (10 : Fin 11) p hp hsplit]
  change (quarticCMCharacterTrace p s.χ
      (fun i => ((d i).val : ZMod p)) s.π).re = _
  exact congrArg Complex.re
    (quarticCMCharacterTrace_eq_eta_norm_fiber_sum p hsplit
      s.ρ s.π s.norm_eq s.real_odd s.imag_even s.kernel_eq
      s.χ s.order_eq s.character_eq
      (fun i => ((d i).val : ZMod p)) (coefficientProduct d) hD hDa)

/-- The same identity without a coefficient-unit hypothesis. The bad-prime
case vanishes on both sides. -/
theorem baseConstituent_ten_split_eq_eta_norm_fiber_all
    (d : Fin 4 → CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hsplit : p % 4 = 1) :
    baseConstituent d (10 : Fin 11) p =
      letI : Fact p.Prime := ⟨hp⟩
      let s := quarticSplitPrimeChoice p hsplit
      (∑ Q ∈ gaussianSplitNormPrimeFiber p s.ρ s.π s.norm_eq s.kernel_eq,
        gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal).re := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := quarticSplitPrimeChoice p hsplit
  have hDa : (coefficientProduct d : ZMod p) =
      ∏ i, ((d i).val : ZMod p) := by
    simp [coefficientProduct]
  rw [baseConstituent_split d (10 : Fin 11) p hp hsplit]
  change (quarticCMCharacterTrace p s.χ
      (fun i => ((d i).val : ZMod p)) s.π).re = _
  exact congrArg Complex.re
    (quarticCMCharacterTrace_eq_eta_norm_fiber_sum_all p hsplit
      s.ρ s.π s.norm_eq s.real_odd s.imag_even s.kernel_eq
      s.χ s.order_eq s.character_eq
      (fun i => ((d i).val : ZMod p)) (coefficientProduct d) hDa)

/-- An inert rational prime cannot be the absolute norm of a Gaussian
ideal, hence cannot occur in a norm-prime ideal fiber. -/
theorem no_gaussian_ideal_norm_mod_four_three
    (p : ℕ) (hinert : p % 4 = 3)
    (I : Ideal (𝓞 GaussianField)) : I.absNorm ≠ p := by
  intro hnorm
  have hgen := gaussianIdealGenerator_norm I
  rw [hnorm] at hgen
  exact prime_gaussian_norm_mod_four_ne_three p
    (gaussianIdealGenerator I) hgen hinert

/-- A single rational-prime CM summand is the sum over the corresponding
prime-ideal norm fiber inside a Gaussian norm cutoff. -/
theorem baseConstituent_ten_eq_primeBox_norm_fiber
    (d : Fin 4 → CanonicalParts) (B p : ℕ)
    (hp : p ∈ quarticBasePrimes B) :
    baseConstituent d (10 : Fin 11) p / (p : ℝ) =
      ∑ Q ∈ (GaussianIdealExponentVectors.primeBox B).filter
        (fun Q => Ideal.absNorm Q.asIdeal = p),
        (gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal).re /
          (Ideal.absNorm Q.asIdeal : ℝ) := by
  classical
  obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hp
  have hle : p ≤ B := (Finset.mem_Icc.mp hIcc).2
  have hthree : 3 ≤ p := (Finset.mem_Icc.mp hIcc).1
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := hprime.odd_of_ne_two (by omega : p ≠ 2)
    omega
  rcases hmod with hsplit | hinert
  · letI : Fact p.Prime := ⟨hprime⟩
    let s := quarticSplitPrimeChoice p hsplit
    have hfiber : gaussianSplitNormPrimeFiber p s.ρ s.π s.norm_eq s.kernel_eq =
        (GaussianIdealExponentVectors.primeBox B).filter
          (fun Q => Ideal.absNorm Q.asIdeal = p) := by
      ext Q
      rw [mem_gaussianSplitNormPrimeFiber_iff, Finset.mem_filter,
        GaussianIdealExponentVectors.mem_primeBox]
      exact ⟨fun h => ⟨h ▸ hle, h⟩, And.right⟩
    rw [baseConstituent_ten_split_eq_eta_norm_fiber_all
      d p hprime hsplit]
    change (∑ Q ∈ gaussianSplitNormPrimeFiber p s.ρ s.π
      s.norm_eq s.kernel_eq,
        gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal).re / (p : ℝ) = _
    rw [hfiber, Complex.re_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [(Finset.mem_filter.mp hQ).2]
  · rw [baseConstituent_inert d (10 : Fin 11) p hprime hinert]
    have hempty : (GaussianIdealExponentVectors.primeBox B).filter
        (fun Q => Ideal.absNorm Q.asIdeal = p) = ∅ := by
      ext Q
      simp only [Finset.mem_filter]
      constructor
      · intro hQ
        exact (no_gaussian_ideal_norm_mod_four_three p hinert Q.asIdeal hQ.2).elim
      · intro hQ
        simp at hQ
    simp [hempty]

/-- A rational prime dividing the radicand annihilates the CM ideal weight
at every Gaussian prime ideal of that norm. -/
theorem gaussianEtaIdealWeight_zero_of_prime_dvd_radicand
    (p : ℕ) (R : ℤ) (hpR : (p : ℤ) ∣ R)
    (ι : GaussianField →+* ℂ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hnorm : Ideal.absNorm P.asIdeal = p) :
    gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal = 0 := by
  obtain ⟨k, hk⟩ := hpR
  have hp : (p : 𝓞 GaussianField) ∈ P.asIdeal := by
    rw [← hnorm]
    exact Ideal.absNorm_mem P.asIdeal
  have hR : (R : 𝓞 GaussianField) ∈ P.asIdeal := by
    rw [hk]
    simpa only [Int.cast_mul, Int.cast_natCast] using
      (P.asIdeal.mul_mem_right (k : 𝓞 GaussianField) hp)
  have hbad : ¬ GaussianQuarticGoodIdeal
      (R : 𝓞 GaussianField) P.asIdeal := by
    intro hgood
    exact (hgood.2 P (dvd_refl _)).2 hR
  simp [gaussianEtaIdealWeight, quarticIdealWeight, hbad]

theorem gaussianEtaIdealWeight_zero_of_absNorm_two
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hnorm : Ideal.absNorm P.asIdeal = 2) :
    gaussianEtaIdealWeight R ι P.asIdeal = 0 := by
  have heven : (P.asIdeal.absNorm : ZMod 2) ≠ 1 := by
    rw [hnorm]
    decide
  simp [gaussianEtaIdealWeight, gaussianNuIdealWeight_of_even _ heven]

/-- The CM constituent's good rational-prime sum is dominated by the full
Gaussian η prime-ideal sum, up to the inert degree-two tail. -/
theorem baseConstituent_ten_good_sum_le_eta_primeBox_add_constant
    (d : Fin 4 → CanonicalParts) (B : ℕ) :
    (∑ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬ p ∣ (d i).val),
      baseConstituent d (10 : Fin 11) p / (p : ℝ)) ≤
      (∑ P ∈ GaussianIdealExponentVectors.primeBox B,
        (gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding P.asIdeal).re /
          (Ideal.absNorm P.asIdeal : ℝ)) +
        reciprocalSquareConstant := by
  classical
  let good : ℕ → Prop := fun p => ∀ i, ¬p ∣ (d i).val
  let c : HeightOneSpectrum (𝓞 GaussianField) → ℝ := fun P =>
    (gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding P.asIdeal).re
  have hsum : (∑ p ∈ (quarticBasePrimes B).filter good,
      baseConstituent d (10 : Fin 11) p / (p : ℝ)) =
      ∑ P ∈ (GaussianIdealExponentVectors.primeBox B).filter
        (fun P => Ideal.absNorm P.asIdeal ∈ (quarticBasePrimes B).filter good),
        c P / (Ideal.absNorm P.asIdeal : ℝ) := by
    calc
      _ = ∑ p ∈ (quarticBasePrimes B).filter good,
          ∑ P ∈ (GaussianIdealExponentVectors.primeBox B).filter
            (fun P => Ideal.absNorm P.asIdeal = p),
            c P / (Ideal.absNorm P.asIdeal : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact baseConstituent_ten_eq_primeBox_norm_fiber d B p
          (Finset.mem_filter.mp hp).1
      _ = _ := Finset.sum_fiberwise_eq_sum_filter
        (GaussianIdealExponentVectors.primeBox B)
        ((quarticBasePrimes B).filter good)
        (fun P => Ideal.absNorm P.asIdeal)
        (fun P => c P / (Ideal.absNorm P.asIdeal : ℝ))
  have hc : ∀ P ∈ GaussianIdealExponentVectors.primeBox B,
      |c P| ≤ 1 := by
    intro P hP
    exact (Complex.abs_re_le_norm _).trans
      (norm_gaussianEtaIdealWeight_le_one _ _ _)
  have hzero : ∀ P ∈ GaussianIdealExponentVectors.primeBox B,
      gaussianDegreeOne P →
      (Ideal.absNorm P.asIdeal = 2 ∨ ¬ good (Ideal.absNorm P.asIdeal)) →
      c P = 0 := by
    intro P hP hdegree hbad
    rcases hbad with htwo | hnotgood
    · simp [c, gaussianEtaIdealWeight_zero_of_absNorm_two _ _ P htwo]
    · obtain ⟨i, hi⟩ := not_forall.mp hnotgood
      have hp : Ideal.absNorm P.asIdeal ∣ (d i).val := by simpa [good] using hi
      have hpD : Ideal.absNorm P.asIdeal ∣ coefficientProduct d :=
        hp.trans (Finset.dvd_prod_of_mem (fun j => (d j).val)
          (Finset.mem_univ i))
      have hpDint : ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) ∣
          (coefficientProduct d : ℤ) := by exact_mod_cast hpD
      have hη := gaussianEtaIdealWeight_zero_of_prime_dvd_radicand
        (Ideal.absNorm P.asIdeal) (coefficientProduct d : ℤ)
          hpDint gaussianCanonicalFieldEmbedding P rfl
      have hη' : gaussianEtaIdealWeight (coefficientProduct d : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding P.asIdeal = 0 := by
        simpa only [Int.cast_natCast] using hη
      simpa [c] using congrArg Complex.re hη'
  rw [hsum]
  simpa only [good, c] using
    (gaussianPrime_goodBaseSum_le_full_add_constant B good c hc hzero)

/-- The direct CM constituent estimate needed in the eleven-term trace. -/
theorem baseConstituent_ten_good_sum_le_coefficient_loglog
    (d : Fin 4 → CanonicalParts) (B : ℕ) (hB : 3 ≤ B) :
    (∑ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬ p ∣ (d i).val),
      baseConstituent d (10 : Fin 11) p / (p : ℝ)) ≤
      Real.log (Real.log (2 * (coefficientProduct d : ℝ))) +
        (Real.log 13 + Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + reciprocalSquareConstant) +
        reciprocalSquareConstant := by
  have hDpos : 0 < coefficientProduct d := by
    unfold coefficientProduct
    exact Finset.prod_pos (fun i _ => CanonicalPart.pos (d i).property)
  have hR0 : (coefficientProduct d : ℤ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hR : (coefficientProduct d : ℤ).natAbs ≤ (coefficientProduct d) ^ 3 := by
    simp only [Int.natAbs_natCast]
    calc
      coefficientProduct d = coefficientProduct d * 1 := by omega
      _ ≤ coefficientProduct d * (coefficientProduct d) ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith)
      _ = (coefficientProduct d) ^ 3 := by ring
  have hBreal : (2 : ℝ) ≤ B := by exact_mod_cast (by omega : 2 ≤ B)
  have hlogB : (1 : ℝ) ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB
    have hlog3 : (1 : ℝ) ≤ Real.log 3 :=
      le_of_lt (lt_trans (by norm_num : (1 : ℝ) < 1.0986122885)
        Real.log_three_gt_d9)
    exact hlog3.trans (Real.log_le_log (by norm_num) h3)
  have hη := etaFinitePrimeSum_le_coefficient_loglog
    (GaussianIdealExponentVectors.primeBox B)
    (coefficientProduct d) hDpos (coefficientProduct d : ℤ) hR0 hR
    gaussianCanonicalFieldEmbedding (B : ℝ) hBreal hlogB
    (fun P hP => GaussianIdealExponentVectors.norm_le_of_mem_primeBox B P hP)
    (fun P => GaussianIdealExponentVectors.norm_gt_of_not_mem_primeBox B
      P.val P.property)
  have htransfer := baseConstituent_ten_good_sum_le_eta_primeBox_add_constant d B
  simp only [Int.cast_natCast] at hη
  linarith

end Erdos940.Quartic.GaussianCMConstituentBridge
