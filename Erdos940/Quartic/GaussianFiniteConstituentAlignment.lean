import Erdos940.Quartic.GaussianCMConstituentBridge
import Erdos940.Quartic.GaussianFiniteRadicandNonpower
import Erdos940.Quartic.GaussianQuarticSymbolCongruence

/-!
# Finite quartic constituents as global ideal-character fibers

The rational radicand of each of the nine finite-order buckets is fixed
globally. Its local reduction agrees with the radicand in the finite-field
trace, so the two Gaussian prime values come from the same global quartic
ideal character.
-/

namespace Erdos940.Quartic.GaussianFiniteConstituentAlignment

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianCMConstituentBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries

theorem quarticIdealWeight_selected_prime_int
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (R : ℤ) (hR : (R : ZMod q) ≠ 0) :
    quarticIdealWeight (R : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ).asIdeal =
        χ (R : ZMod q) := by
  have hρR : ρ (R : GaussianInt) = (R : ZMod q) := by simp
  have hRingR : (R : 𝓞 GaussianField) =
      gaussianFourthIntegerRingEquiv (R : GaussianInt) := by simp
  rw [hRingR]
  simpa only [hρR] using
    quarticIdealWeight_selected_prime_eq_character q hqmod ρ π hπ0 hρπ
      χ hχ hρchar (R : GaussianInt) (hρR ▸ hR)

theorem quarticIdealWeight_conjugate_prime_int
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (R : ℤ) (hR : (R : ZMod q) ≠ 0) :
    quarticIdealWeight (R : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding
      (gaussianPrimeIdealOfReduction q
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π hπ0)
        (conjugateGaussianReduction_star_prime q ρ π hρπ)).asIdeal =
        (χ (R : ZMod q))⁻¹ := by
  have hχinv : orderOf χ⁻¹ = 4 := by
    simpa [hχ] using (orderOf_inv χ)
  have hρcharbar :=
    conjugateReduction_matches_inverse_character q ρ χ hχ hρchar
  have hρR : conjugateGaussianReduction q ρ (R : GaussianInt) =
      (R : ZMod q) := by simp [conjugateGaussianReduction, starRingEnd_apply]
  have hRingR : (R : 𝓞 GaussianField) =
      gaussianFourthIntegerRingEquiv (R : GaussianInt) := by simp
  rw [hRingR]
  have h := quarticIdealWeight_selected_prime_eq_character q hqmod
    (conjugateGaussianReduction q ρ) (star π)
    (conjugate_gaussian_prime_ne_zero π hπ0)
    (conjugateGaussianReduction_star_prime q ρ π hρπ)
    χ⁻¹ hχinv hρcharbar (R : GaussianInt) (hρR ▸ hR)
  simpa only [hρR, MulChar.inv_apply_eq_inv'] using h

/-- Both prime-ideal terms of a finite rational quartic trace come from
the same signed integer global radicand. -/
theorem quarticRationalPrimeSymbolTrace_eq_global_ideal_fiber
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (R : ℤ) (hR : (R : ZMod q) ≠ 0) :
    quarticRationalPrimeSymbolTrace q hqmod ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π)) (R : ZMod q) hR =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        quarticIdealWeight (R : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal := by
  classical
  let hπ0 := gaussianPrime_ne_zero_of_norm q π hπnorm
  let hρπ := (hker π).2 (dvd_refl π)
  have hne := conjugateGaussianPrimeIdeal_ne
    q ρ π hπnorm hπre hπim hker
  rw [gaussianSplitNormPrimeFiber, Finset.sum_pair hne,
    quarticIdealWeight_selected_prime_int q hqmod ρ π hπ0 hρπ
      χ hχ hρchar R hR,
    quarticIdealWeight_conjugate_prime_int q hqmod ρ π hπ0 hρπ
      χ hχ hρchar R hR]
  unfold quarticRationalPrimeSymbolTrace
  rw [quarticRationalPrimeSymbolValue_eq_character
    q hqmod ρ π hπ0 hρπ χ hχ hρchar (R : ZMod q) hR]

/-- A finite-order eleven-series constituent is a global ideal-character
trace over the complete norm-`q` fiber. -/
theorem quarticElevenCharacterConstituent_finite_eq_global_fiber
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (d : Fin 4 → CanonicalParts)
    (hunit : ∀ i, ((d i).val : ZMod q) ≠ 0)
    (j : Fin 11) (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
    quarticElevenCharacterConstituent q χ
        (fun i => ((d i).val : ZMod q)) π j =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        quarticIdealWeight
          (finiteConstituentRadicand d j : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal := by
  let a : Fin 4 → ZMod q := fun i => ((d i).val : ZMod q)
  have hr : (finiteConstituentRadicand d j : ZMod q) ≠ 0 := by
    rw [finiteConstituentRadicand_cast]
    exact quarticFiniteBucketRadicand_ne_zero q a hunit j
  have htrace := quarticElevenPrimeSymbolConstituent_finite_eq_trace
    q hqmod ρ π
    (gaussianPrime_ne_zero_of_norm q π hπnorm)
    ((hker π).2 (dvd_refl π)) χ a hunit j hj
  have hchar := quarticElevenCharacterConstituent_eq_prime_symbol
    q hqmod ρ π
    (gaussianPrime_ne_zero_of_norm q π hπnorm)
    ((hker π).2 (dvd_refl π)) χ hχ hρchar a hunit j
  rw [hchar, htrace]
  simpa only [a, ← finiteConstituentRadicand_cast] using
    quarticRationalPrimeSymbolTrace_eq_global_ideal_fiber
      q hqmod ρ π hπnorm hπre hπim hker χ hχ hρchar
      (finiteConstituentRadicand d j) hr

theorem baseConstituent_finite_split_eq_global_fiber
    (d : Fin 4 → CanonicalParts) (j : Fin 11)
    (hj : 1 ≤ j.val ∧ j.val ≤ 9)
    (p : ℕ) (hp : p.Prime) (hsplit : p % 4 = 1)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    baseConstituent d j p =
      letI : Fact p.Prime := ⟨hp⟩
      let s := quarticSplitPrimeChoice p hsplit
      (∑ Q ∈ gaussianSplitNormPrimeFiber p s.ρ s.π
        s.norm_eq s.kernel_eq,
        quarticIdealWeight
          (finiteConstituentRadicand d j : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal).re := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := quarticSplitPrimeChoice p hsplit
  rw [baseConstituent_split d j p hp hsplit]
  exact congrArg Complex.re
    (quarticElevenCharacterConstituent_finite_eq_global_fiber
      p hsplit s.ρ s.π s.norm_eq s.real_odd s.imag_even
      s.kernel_eq s.χ s.order_eq s.character_eq d hunit j hj)

/-- A rational prime dividing the signed radicand makes the quartic ideal
weight vanish at every Gaussian prime ideal of that absolute norm. -/
theorem quarticIdealWeight_eq_zero_of_prime_dvd_radicand
    (p : ℕ) (R : ℤ) (hpR : (p : ℤ) ∣ R)
    (ι : GaussianField →+* ℂ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hnorm : Ideal.absNorm P.asIdeal = p) :
    quarticIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal = 0 := by
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
  simp [quarticIdealWeight, hbad]

theorem quarticIdealWeight_eq_zero_of_absNorm_two
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hnorm : Ideal.absNorm P.asIdeal = 2) :
    quarticIdealWeight R ι P.asIdeal = 0 := by
  have hbad : ¬ GaussianQuarticGoodIdeal R P.asIdeal := by
    intro hgood
    have hcop := (hgood.2 P (dvd_refl _)).1
    rw [hnorm] at hcop
    norm_num at hcop
  simp [quarticIdealWeight, hbad]

/-- At every good base prime, including an inert prime whose Gaussian
norm-`p` fiber is empty, the rational constituent equals its global
ideal-character norm fiber. -/
theorem baseConstituent_finite_eq_primeBox_norm_fiber
    (d : Fin 4 → CanonicalParts) (j : Fin 11)
    (hj : 1 ≤ j.val ∧ j.val ≤ 9)
    (B p : ℕ)
    (hp : p ∈ quarticBasePrimes B)
    (hgood : ∀ i, ¬ p ∣ (d i).val) :
    baseConstituent d j p / (p : ℝ) =
      ∑ Q ∈ (GaussianIdealExponentVectors.primeBox B).filter
        (fun Q => Ideal.absNorm Q.asIdeal = p),
        (quarticIdealWeight
          (finiteConstituentRadicand d j : 𝓞 GaussianField)
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
    have hunit : ∀ i, ((d i).val : ZMod p) ≠ 0 := by
      intro i hi
      exact hgood i ((ZMod.natCast_eq_zero_iff (d i).val p).mp hi)
    have hfiber : gaussianSplitNormPrimeFiber p s.ρ s.π s.norm_eq s.kernel_eq =
        (GaussianIdealExponentVectors.primeBox B).filter
          (fun Q => Ideal.absNorm Q.asIdeal = p) := by
      ext Q
      rw [mem_gaussianSplitNormPrimeFiber_iff, Finset.mem_filter,
        GaussianIdealExponentVectors.mem_primeBox]
      exact ⟨fun h => ⟨h ▸ hle, h⟩, And.right⟩
    rw [baseConstituent_finite_split_eq_global_fiber
      d j hj p hprime hsplit hunit]
    change (∑ Q ∈ gaussianSplitNormPrimeFiber p s.ρ s.π
      s.norm_eq s.kernel_eq,
        quarticIdealWeight
          (finiteConstituentRadicand d j : 𝓞 GaussianField)
          gaussianCanonicalFieldEmbedding Q.asIdeal).re / (p : ℝ) = _
    rw [hfiber, Complex.re_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [(Finset.mem_filter.mp hQ).2]
  · rw [baseConstituent_inert d j p hprime hinert]
    have hj0 : j ≠ 0 := by
      intro hz
      subst j
      omega
    have hempty : (GaussianIdealExponentVectors.primeBox B).filter
        (fun Q => Ideal.absNorm Q.asIdeal = p) = ∅ := by
      ext Q
      simp only [Finset.mem_filter]
      constructor
      · intro hQ
        exact (no_gaussian_ideal_norm_mod_four_three p hinert Q.asIdeal hQ.2).elim
      · intro hQ
        simp at hQ
    simp [hj0, hempty]

end Erdos940.Quartic.GaussianFiniteConstituentAlignment
