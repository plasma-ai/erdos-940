import Erdos940.Quartic.GaussianConjugateSymbol

/-!
# Finite quartic constituents as Gaussian-prime fiber sums

At a split prime, each of the three complementary-pair and six mixed
constituents is the sum of its quartic ideal-symbol values at all Gaussian
prime ideals of rational norm q.
-/

namespace Erdos940.Quartic

open NumberField IsDedekindDomain
open scoped BigOperators

/-- The two Gaussian primes over a split rational prime, presented as a
finite set. The membership theorem below characterizes it independently
by absolute norm. -/
noncomputable def gaussianSplitNormPrimeFiber
    (q : ℕ) [Fact q.Prime] (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z) :
    Finset (HeightOneSpectrum (𝓞 GaussianField)) := by
  classical
  exact {(gaussianPrimeIdealOfReduction q ρ π
      (gaussianPrime_ne_zero_of_norm q π hπnorm)
      ((hker π).2 (dvd_refl π))),
   (gaussianPrimeIdealOfReduction q
      (conjugateGaussianReduction q ρ) (star π)
      (conjugate_gaussian_prime_ne_zero π
        (gaussianPrime_ne_zero_of_norm q π hπnorm))
      (conjugateGaussianReduction_star_prime q ρ π
        ((hker π).2 (dvd_refl π))))}

theorem mem_gaussianSplitNormPrimeFiber_iff
    (q : ℕ) [Fact q.Prime] (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (Q : HeightOneSpectrum (𝓞 GaussianField)) :
    Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker ↔
      Ideal.absNorm Q.asIdeal = q := by
  rw [gaussianSplitNormPrimeFiber]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact gaussianPrimeIdealOfReduction_absNorm q ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π))
    · exact gaussianPrimeIdealOfReduction_absNorm q
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π
          (gaussianPrime_ne_zero_of_norm q π hπnorm))
        (conjugateGaussianReduction_star_prime q ρ π
          ((hker π).2 (dvd_refl π)))
  · intro hNorm
    exact (gaussian_split_prime_fiber_iff q ρ π hπnorm hker Q).1
      (gaussianBasePrime_eq_of_absNorm_eq_prime q Q hNorm)

/-- The actual quartic prime-ideal symbol on a rational radicand at any
prime ideal of absolute norm q. -/
noncomputable def quarticRationalIdealSymbolWeight
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (r : ZMod q) (hr : r ≠ 0)
    (Q : HeightOneSpectrum (𝓞 GaussianField))
    (hNorm : Ideal.absNorm Q.asIdeal = q) : ℂ := by
  let z : GaussianInt := (r.val : ℕ)
  have h2 : (Ideal.absNorm Q.asIdeal).Coprime 4 := by
    rw [hNorm]
    apply Nat.coprime_of_mul_modEq_one 1
    change q * 1 % 4 = 1 % 4
    omega
  have hR : gaussianFourthIntegerRingEquiv z ∉ Q.asIdeal := by
    have hfiber := (gaussian_split_prime_fiber_iff
      q ρ π hπnorm hker Q).1
        (gaussianBasePrime_eq_of_absNorm_eq_prime q Q hNorm)
    rcases hfiber with hQ | hQ
    · subst Q
      have hz : ρ z ≠ 0 := by simpa [z] using hr
      exact gaussianPrimeIdealOfReduction_not_mem q ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π)) z hz
    · subst Q
      have hz : conjugateGaussianReduction q ρ z ≠ 0 := by
        simpa [conjugateGaussianReduction, z, starRingEnd_apply] using hr
      exact gaussianPrimeIdealOfReduction_not_mem q
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π
          (gaussianPrime_ne_zero_of_norm q π hπnorm))
        (conjugateGaussianReduction_star_prime q ρ π
          ((hker π).2 (dvd_refl π))) z hz
  exact fourthIntegerRingToComplex
    (((gaussianQuarticPrimeSymbol (gaussianFourthIntegerRingEquiv z)
        Q h2 hR : rootsOfUnity 4 (𝓞 GaussianField)) :
        (𝓞 GaussianField)ˣ) : 𝓞 GaussianField)

theorem quarticRationalIdealSymbolWeight_first_prime
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (r : ZMod q) (hr : r ≠ 0) :
    quarticRationalIdealSymbolWeight q hqmod ρ π hπnorm hker r hr
        (gaussianPrimeIdealOfReduction q ρ π
          (gaussianPrime_ne_zero_of_norm q π hπnorm)
          ((hker π).2 (dvd_refl π)))
        (gaussianPrimeIdealOfReduction_absNorm q ρ π
          (gaussianPrime_ne_zero_of_norm q π hπnorm)
          ((hker π).2 (dvd_refl π))) =
      quarticRationalPrimeSymbolValue q hqmod ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π)) r hr := by
  rfl

theorem quarticRationalIdealSymbolWeight_conjugate_prime
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (r : ZMod q) (hr : r ≠ 0) :
    quarticRationalIdealSymbolWeight q hqmod ρ π hπnorm hker r hr
        (gaussianPrimeIdealOfReduction q
          (conjugateGaussianReduction q ρ) (star π)
          (conjugate_gaussian_prime_ne_zero π
            (gaussianPrime_ne_zero_of_norm q π hπnorm))
          (conjugateGaussianReduction_star_prime q ρ π
            ((hker π).2 (dvd_refl π))))
        (gaussianPrimeIdealOfReduction_absNorm q
          (conjugateGaussianReduction q ρ) (star π)
          (conjugate_gaussian_prime_ne_zero π
            (gaussianPrime_ne_zero_of_norm q π hπnorm))
          (conjugateGaussianReduction_star_prime q ρ π
            ((hker π).2 (dvd_refl π)))) =
      quarticRationalPrimeSymbolValue q hqmod
        (conjugateGaussianReduction q ρ) (star π)
        (conjugate_gaussian_prime_ne_zero π
          (gaussianPrime_ne_zero_of_norm q π hπnorm))
        (conjugateGaussianReduction_star_prime q ρ π
          ((hker π).2 (dvd_refl π))) r hr := by
  rfl

/-- Extend the ideal-symbol weight by zero away from the norm-q fiber. -/
noncomputable def quarticRationalIdealSymbolWeightTotal
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (r : ZMod q) (hr : r ≠ 0)
    (Q : HeightOneSpectrum (𝓞 GaussianField)) : ℂ :=
  if hNorm : Ideal.absNorm Q.asIdeal = q then
    quarticRationalIdealSymbolWeight q hqmod ρ π hπnorm hker r hr Q hNorm
  else 0

/-- A rational finite-order quartic trace is the sum of its actual
ideal-symbol weights over every Gaussian prime ideal of norm q. -/
theorem quarticRationalPrimeSymbolTrace_eq_norm_fiber_sum
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (r : ZMod q) (hr : r ≠ 0) :
    quarticRationalPrimeSymbolTrace q hqmod ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π)) r hr =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        quarticRationalIdealSymbolWeightTotal q hqmod ρ π hπnorm hker
          r hr Q := by
  classical
  have hne := conjugateGaussianPrimeIdeal_ne
    q ρ π hπnorm hπre hπim hker
  rw [gaussianSplitNormPrimeFiber, Finset.sum_pair hne]
  simp only [quarticRationalIdealSymbolWeightTotal,
    dif_pos (gaussianPrimeIdealOfReduction_absNorm q ρ π
      (gaussianPrime_ne_zero_of_norm q π hπnorm)
      ((hker π).2 (dvd_refl π))),
    dif_pos (gaussianPrimeIdealOfReduction_absNorm q
      (conjugateGaussianReduction q ρ) (star π)
      (conjugate_gaussian_prime_ne_zero π
        (gaussianPrime_ne_zero_of_norm q π hπnorm))
          (conjugateGaussianReduction_star_prime q ρ π
        ((hker π).2 (dvd_refl π))))]
  rw [quarticRationalIdealSymbolWeight_first_prime,
    quarticRationalIdealSymbolWeight_conjugate_prime]
  exact quarticRationalPrimeSymbolTrace_eq_two_primes
    q hqmod ρ π
    (gaussianPrime_ne_zero_of_norm q π hπnorm)
    ((hker π).2 (dvd_refl π))
    χ hχ hρchar r hr

/-- Rational radicands of the nine finite-order buckets. The values at
indices zero and ten are harmless defaults, because those buckets are
quadratic and CM rather than quartic finite-order symbols. -/
def quarticFiniteBucketRadicand
    (q : ℕ) (a : Fin 4 → ZMod q) : Fin 11 → ZMod q
  | 0 => 1
  | 1 => quarticPairRadicand q a (quarticPairRepresentative 0)
  | 2 => quarticPairRadicand q a (quarticPairRepresentative 1)
  | 3 => quarticPairRadicand q a (quarticPairRepresentative 2)
  | 4 => quarticMixedRadicand q a (quarticMixedRepresentative 0)
  | 5 => quarticMixedRadicand q a (quarticMixedRepresentative 1)
  | 6 => quarticMixedRadicand q a (quarticMixedRepresentative 2)
  | 7 => quarticMixedRadicand q a (quarticMixedRepresentative 3)
  | 8 => quarticMixedRadicand q a (quarticMixedRepresentative 4)
  | 9 => quarticMixedRadicand q a (quarticMixedRepresentative 5)
  | _ => 1

theorem quarticFiniteBucketRadicand_ne_zero
    (q : ℕ) [Fact q.Prime]
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (k : Fin 11) :
    quarticFiniteBucketRadicand q a k ≠ 0 := by
  fin_cases k <;>
    simp [quarticFiniteBucketRadicand, quarticPairRadicand_ne_zero,
      quarticMixedRadicand_ne_zero, ha]

theorem quarticElevenPrimeSymbolConstituent_finite_eq_trace
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (k : Fin 11) (hk : 1 ≤ k.val ∧ k.val ≤ 9) :
    quarticElevenPrimeSymbolConstituent q hqmod ρ π hπ0 hρπ χ a ha k =
      quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
        (quarticFiniteBucketRadicand q a k)
        (quarticFiniteBucketRadicand_ne_zero q a ha k) := by
  fin_cases k <;>
    simp_all [quarticElevenPrimeSymbolConstituent,
      quarticFiniteBucketRadicand]

/-- Each of the nine finite quartic constituents is a sum of genuine
prime-ideal symbol values over the complete norm-q Gaussian-prime fiber. -/
theorem quarticElevenPrimeSymbolConstituent_finite_eq_norm_fiber_sum
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (k : Fin 11) (hk : 1 ≤ k.val ∧ k.val ≤ 9) :
    quarticElevenPrimeSymbolConstituent q hqmod ρ π
        (gaussianPrime_ne_zero_of_norm q π hπnorm)
        ((hker π).2 (dvd_refl π)) χ a ha k =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        quarticRationalIdealSymbolWeightTotal q hqmod ρ π hπnorm hker
          (quarticFiniteBucketRadicand q a k)
          (quarticFiniteBucketRadicand_ne_zero q a ha k) Q := by
  rw [quarticElevenPrimeSymbolConstituent_finite_eq_trace
    q hqmod ρ π (gaussianPrime_ne_zero_of_norm q π hπnorm)
    ((hker π).2 (dvd_refl π)) χ a ha k hk]
  exact quarticRationalPrimeSymbolTrace_eq_norm_fiber_sum
    q hqmod ρ π hπnorm hπre hπim hker χ hχ hρchar
    (quarticFiniteBucketRadicand q a k)
    (quarticFiniteBucketRadicand_ne_zero q a ha k)

/-- The same norm-fiber formula for the character constituents used in
the global eleven-series construction. -/
theorem quarticElevenCharacterConstituent_finite_eq_norm_fiber_sum
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (k : Fin 11) (hk : 1 ≤ k.val ∧ k.val ≤ 9) :
    quarticElevenCharacterConstituent q χ a π k =
      ∑ Q ∈ gaussianSplitNormPrimeFiber q ρ π hπnorm hker,
        quarticRationalIdealSymbolWeightTotal q hqmod ρ π hπnorm hker
          (quarticFiniteBucketRadicand q a k)
          (quarticFiniteBucketRadicand_ne_zero q a ha k) Q := by
  rw [quarticElevenCharacterConstituent_eq_prime_symbol
    q hqmod ρ π (gaussianPrime_ne_zero_of_norm q π hπnorm)
    ((hker π).2 (dvd_refl π)) χ hχ hρchar a ha k]
  exact quarticElevenPrimeSymbolConstituent_finite_eq_norm_fiber_sum
    q hqmod ρ π hπnorm hπre hπim hker χ hχ hρchar a ha k hk

end Erdos940.Quartic
