import Erdos940.Quartic.GaussianConductorComplete

/-!
# The Gaussian quartic character of two

The quartic symbol with numerator `2` is trivial on principal ideals whose
generator is one modulo `64`. The proof uses the global Hilbert product
formula. At every place away from `2`, the numerator is a unit, so the local
Hilbert factor is the corresponding quartic residue factor. The generator
has a fourth root at the places over `2`.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols

namespace Erdos940.Quartic

private abbrev twoQuarticLevel : ℕ+ := ⟨4, by decide⟩

private theorem twoPrimitiveFourthRoots :
    (primitiveRoots 4 GaussianField).Nonempty := by
  letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) ℚ GaussianField
      (Set.mem_singleton 4) (by decide : 4 ≠ 0)
  exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 4)).2 hζ⟩

private theorem two_not_mem_of_not_exponent
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField twoQuarticLevel) :
    ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal := by
  intro htwo
  apply hP
  rw [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
    GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal,
    Ideal.dvd_span_singleton]
  have hpow := (P.isPrime.pow_mem_iff_mem 2 (by decide)).2 htwo
  have heq : (((2 : ℕ) : 𝓞 GaussianField) ^ 2) = 4 := by norm_num
  change (4 : 𝓞 GaussianField) ∈ P.asIdeal
  rw [← heq]
  exact hpow

private theorem twoPrime_away_from_exponent
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hcop : (Ideal.absNorm P.asIdeal).Coprime 4) :
    P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField twoQuarticLevel := by
  intro hbad
  have hdiv : P.asIdeal ∣ Ideal.span {((4 : ℕ) : 𝓞 GaussianField)} := by
    simpa [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
      GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal, twoQuarticLevel] using hbad
  have hnormdvd : Ideal.absNorm P.asIdeal ∣
      4 ^ Module.finrank ℤ (𝓞 GaussianField) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdiv)
  have hcop' : (Ideal.absNorm P.asIdeal).Coprime
      (4 ^ Module.finrank ℤ (𝓞 GaussianField)) := hcop.pow_right _
  have hone : Ideal.absNorm P.asIdeal = 1 :=
    (Nat.gcd_eq_left_iff_dvd.mpr hnormdvd).symm.trans hcop'
  exact (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) hone

private theorem dyadicSupported_away_factor_eq_ideal_factor
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hgood : GaussianQuarticGoodIdeal a (Ideal.span {b}))
    (haway : ∀ P : HeightOneSpectrum (𝓞 GaussianField),
      P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel → a ∉ P.asIdeal)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (if P ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel then 1 else
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        GaussianField twoQuarticLevel (by norm_num)
        twoPrimitiveFourthRoots P
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit GaussianField
          a ha0)
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit GaussianField
          b hb0)) =
    GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField (twoQuarticLevel : ℕ)
      (idealPowerResidueFactor GaussianField (Ideal.span {b}) twoQuarticLevel
        twoPrimitiveFourthRoots a
        (fun Q hQ => (hgood.2 Q hQ).1)
        (fun Q hQ => (hgood.2 Q hQ).2) P) := by
  by_cases hPexp : P ∈
      GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel
  · have hPnot : ¬ P.asIdeal ∣ Ideal.span {b} := by
      intro hdiv
      have hcop := (hgood.2 P hdiv).1
      have haway := twoPrime_away_from_exponent P hcop
      exact haway hPexp
    rw [ite_eq_left hPexp]
    simp only [idealPowerResidueFactor, dite_eq_right hPnot]
    exact (GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField (twoQuarticLevel : ℕ)).map_one.symm
  · have ha := haway P hPexp
    by_cases hdiv : P.asIdeal ∣ Ideal.span {b}
    · have hcop := (hgood.2 P hdiv).1
      have hfactor :=
        GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_integral_eq_primeIdealPowerResidueFactor
          GaussianField twoQuarticLevel (by norm_num)
          twoPrimitiveFourthRoots P hPexp hcop
          a b ha0 hb0 ha
      rw [ite_eq_right hPexp]
      simp only [idealPowerResidueFactor, dite_eq_left hdiv, map_pow]
      exact hfactor
    · have hb : b ∉ P.asIdeal := by
        intro hbmem
        apply hdiv
        exact Ideal.dvd_span_singleton.mpr hbmem
      have hone :=
        GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_integral_units_eq_one
          GaussianField twoQuarticLevel (by norm_num)
          twoPrimitiveFourthRoots P hPexp
          a b ha0 hb0 ha hb
      rw [ite_eq_right hPexp]
      simp only [idealPowerResidueFactor, dite_eq_right hdiv]
      exact hone.trans
        (GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
          GaussianField (twoQuarticLevel : ℕ)).map_one.symm

/-- At every tame place, the Hilbert product for a numerator supported at
the dyadic place is its quartic residue character. -/
theorem gaussianDyadicSupported_away_product_eq_ideal_symbol
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hgood : GaussianQuarticGoodIdeal a (Ideal.span {b}))
    (haway : ∀ P : HeightOneSpectrum (𝓞 GaussianField),
      P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel → a ∉ P.asIdeal) :
    GlobalClassFieldTheory.Reciprocity.powerResidueAwayFromExponentFiniteProduct
      GaussianField twoQuarticLevel (by norm_num) twoPrimitiveFourthRoots
      (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit GaussianField
        a ha0)
      (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit GaussianField
        b hb0) =
    GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField (twoQuarticLevel : ℕ)
      (gaussianQuarticIdealSymbol a
        (Ideal.span {b}) hgood) := by
  let f := GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
    GaussianField (twoQuarticLevel : ℕ)
  let g := idealPowerResidueFactor GaussianField (Ideal.span {b}) twoQuarticLevel
    twoPrimitiveFourthRoots a
    (fun Q hQ => (hgood.2 Q hQ).1)
    (fun Q hQ => (hgood.2 Q hQ).2)
  have hfinite : Function.HasFiniteMulSupport g :=
    idealPowerResidueFactor_hasFiniteMulSupport GaussianField
      (Ideal.span {b}) hgood.1 twoQuarticLevel twoPrimitiveFourthRoots
      a
      (fun Q hQ => (hgood.2 Q hQ).1)
      (fun Q hQ => (hgood.2 Q hQ).2)
  have hsymbol : gaussianQuarticIdealSymbol a
      (Ideal.span {b}) hgood = ∏ᶠ P, g P :=
    idealPowerResidueSymbol_eq_finprod GaussianField
      (Ideal.span {b}) hgood.1 twoQuarticLevel twoPrimitiveFourthRoots
      a
      (fun Q hQ => (hgood.2 Q hQ).1)
      (fun Q hQ => (hgood.2 Q hQ).2)
  calc
    _ = ∏ᶠ P, f (g P) := by
      unfold GlobalClassFieldTheory.Reciprocity.powerResidueAwayFromExponentFiniteProduct
      apply finprod_congr
      intro P
      exact dyadicSupported_away_factor_eq_ideal_factor a b ha0 hb0 hgood haway P
    _ = f (∏ᶠ P, g P) := (MonoidHom.map_finprod f hfinite).symm
    _ = f (gaussianQuarticIdealSymbol a
        (Ideal.span {b}) hgood) := congrArg f hsymbol.symm

/-- A Gaussian principal generator equal to one modulo rational `64`
has trivial quartic symbol for every numerator supported at the dyadic place. -/
theorem gaussianDyadicSupportedPrincipalSymbol_eq_one
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hgood : GaussianQuarticGoodIdeal a (Ideal.span {b}))
    (haAway : ∀ P : HeightOneSpectrum (𝓞 GaussianField),
      P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel → a ∉ P.asIdeal)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    gaussianQuarticIdealSymbol a
      (Ideal.span {b}) hgood = 1 := by
  let a' := GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit
    GaussianField a ha0
  let b' := GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit
    GaussianField b hb0
  have hroot : ∀ v : HeightOneSpectrum (𝓞 GaussianField),
      v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel →
      ∃ u : (HeightOneSpectrum.adicAbv GaussianField v).Completionˣ,
        u ^ 4 = GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
          GaussianField v b' := by
    intro v hv
    exact gaussianLocalFourthRoot_to_unit v b hb0
      (gaussianDyadic_exists_fourth_root v hv b h64)
  have hcorr :
      GlobalClassFieldTheory.Reciprocity.powerResidueBadPlaceCorrection
        GaussianField twoQuarticLevel (by norm_num)
        twoPrimitiveFourthRoots a' b' = 1 :=
    gaussianCorrection_eq_one_of_local_fourth_powers a' b' hroot
  have haway :=
    GlobalClassFieldTheory.Reciprocity.powerResidueAwayFromExponentFiniteProduct_eq_badPlaceCorrection_inv
      GaussianField twoQuarticLevel (by norm_num)
      twoPrimitiveFourthRoots a' b'
  rw [hcorr, inv_one] at haway
  have hsymbol := gaussianDyadicSupported_away_product_eq_ideal_symbol
    a b ha0 hb0 hgood haAway
  have hmap :
      GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
        GaussianField (twoQuarticLevel : ℕ)
          (gaussianQuarticIdealSymbol a
            (Ideal.span {b}) hgood) =
        GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
          GaussianField (twoQuarticLevel : ℕ) 1 := by
    rw [← hsymbol]
    simpa only [a', b', map_one] using haway
  exact (GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots_injective
    GaussianField (twoQuarticLevel : ℕ)) hmap

/-- Congruence to one modulo rational `64` makes a Gaussian principal ideal
admissible for the quartic symbol of `2`. -/
theorem gaussianQuarticTwoGoodIdeal_of_sixtyfour_congruence
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    GaussianQuarticGoodIdeal ((2 : ℕ) : 𝓞 GaussianField)
      (Ideal.span {b}) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h64
  have h2 : b - 1 ∈ Ideal.span {((2 : ℕ) : 𝓞 GaussianField)} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(32 : 𝓞 GaussianField) * c, ?_⟩
    calc
      b - 1 = (64 : 𝓞 GaussianField) * c := hc
      _ = (2 : 𝓞 GaussianField) * ((32 : 𝓞 GaussianField) * c) := by ring
  exact gaussianQuarticGoodIdeal_of_principal_congruences
    ((2 : ℕ) : 𝓞 GaussianField) b hb0 h2 h64

/-- The quartic character of `2` has principal period rational `64`. -/
theorem gaussianQuarticTwoSymbol_eq_one_of_sixtyfour_congruence
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    gaussianQuarticIdealSymbol ((2 : ℕ) : 𝓞 GaussianField)
      (Ideal.span {b})
      (gaussianQuarticTwoGoodIdeal_of_sixtyfour_congruence b hb0 h64) = 1 :=
  gaussianDyadicSupportedPrincipalSymbol_eq_one
    ((2 : ℕ) : 𝓞 GaussianField) b (by norm_num) hb0
    (gaussianQuarticTwoGoodIdeal_of_sixtyfour_congruence b hb0 h64)
    (fun P hP => two_not_mem_of_not_exponent P hP) h64

/-- A numerator with no prime divisor away from the dyadic places is
admissible at every Gaussian principal denominator equal to one modulo `64`. -/
theorem gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
    (a b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (haAway : ∀ P : HeightOneSpectrum (𝓞 GaussianField),
      P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel → a ∉ P.asIdeal)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    GaussianQuarticGoodIdeal a (Ideal.span {b}) := by
  have htwo := gaussianQuarticTwoGoodIdeal_of_sixtyfour_congruence b hb0 h64
  refine ⟨htwo.1, ?_⟩
  intro P hPb
  have hcop := (htwo.2 P hPb).1
  exact ⟨hcop, haAway P (twoPrime_away_from_exponent P hcop)⟩

/-- Every quartic numerator whose prime support lies above two has
principal period rational `64`. -/
theorem gaussianDyadicSupportedSymbol_eq_one_of_sixtyfour_congruence
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (haAway : ∀ P : HeightOneSpectrum (𝓞 GaussianField),
      P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField twoQuarticLevel → a ∉ P.asIdeal)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    gaussianQuarticIdealSymbol a (Ideal.span {b})
      (gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
        a b hb0 haAway h64) = 1 :=
  gaussianDyadicSupportedPrincipalSymbol_eq_one a b ha0 hb0
    (gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
      a b hb0 haAway h64) haAway h64

private theorem gaussianNegativeOne_away
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
  intro hneg
  have h1 : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
    simpa only [neg_neg] using P.asIdeal.neg_mem hneg
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one P.asIdeal).mpr h1)

/-- The quartic symbol of `-1` has principal period rational `64`. -/
theorem gaussianQuarticNegativeOneSymbol_eq_one_of_sixtyfour_congruence
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    gaussianQuarticIdealSymbol (-1 : 𝓞 GaussianField) (Ideal.span {b})
      (gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
        (-1 : 𝓞 GaussianField) b hb0
        (fun P _ => gaussianNegativeOne_away P) h64) = 1 :=
  gaussianDyadicSupportedSymbol_eq_one_of_sixtyfour_congruence
    (-1 : 𝓞 GaussianField) b (by norm_num) hb0
    (fun P _ => gaussianNegativeOne_away P) h64

private theorem gaussianTwoPower_away
    (k : ℕ) (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField twoQuarticLevel) :
    (((2 : ℕ) : 𝓞 GaussianField) ^ k) ∉ P.asIdeal := by
  intro hpow
  by_cases hk : k = 0
  · subst k
    have h1 : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by simpa using hpow
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one P.asIdeal).mpr h1)
  · have htwo : ((2 : ℕ) : 𝓞 GaussianField) ∈ P.asIdeal :=
      (P.isPrime.pow_mem_iff_mem k (Nat.pos_of_ne_zero hk)).mp hpow
    exact two_not_mem_of_not_exponent P hP htwo

/-- Every power of two has the same principal period for its quartic symbol. -/
theorem gaussianQuarticTwoPowerSymbol_eq_one_of_sixtyfour_congruence
    (k : ℕ) (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    gaussianQuarticIdealSymbol (((2 : ℕ) : 𝓞 GaussianField) ^ k)
      (Ideal.span {b})
      (gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
        (((2 : ℕ) : 𝓞 GaussianField) ^ k) b hb0
        (gaussianTwoPower_away k) h64) = 1 :=
  gaussianDyadicSupportedSymbol_eq_one_of_sixtyfour_congruence
    (((2 : ℕ) : 𝓞 GaussianField) ^ k) b
    (pow_ne_zero k (by norm_num)) hb0 (gaussianTwoPower_away k) h64

private theorem gaussianNegativeTwoPower_away
    (k : ℕ) (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField twoQuarticLevel) :
    -(((2 : ℕ) : 𝓞 GaussianField) ^ k) ∉ P.asIdeal := by
  intro hneg
  have hpow : (((2 : ℕ) : 𝓞 GaussianField) ^ k) ∈ P.asIdeal := by
    simpa only [neg_neg] using P.asIdeal.neg_mem hneg
  exact gaussianTwoPower_away k P hP hpow

/-- Signed powers of two have principal period rational `64`. -/
theorem gaussianQuarticNegativeTwoPowerSymbol_eq_one_of_sixtyfour_congruence
    (k : ℕ) (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    gaussianQuarticIdealSymbol (-(((2 : ℕ) : 𝓞 GaussianField) ^ k))
      (Ideal.span {b})
      (gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
        (-(((2 : ℕ) : 𝓞 GaussianField) ^ k)) b hb0
        (gaussianNegativeTwoPower_away k) h64) = 1 :=
  gaussianDyadicSupportedSymbol_eq_one_of_sixtyfour_congruence
    (-(((2 : ℕ) : 𝓞 GaussianField) ^ k)) b
    (neg_ne_zero.mpr (pow_ne_zero k (by norm_num))) hb0
    (gaussianNegativeTwoPower_away k) h64

/-- A denominator admissible for two quartic numerators is admissible for
their product. -/
theorem gaussianQuarticGoodIdeal_mul_numerator
    (a c : 𝓞 GaussianField) (I : Ideal (𝓞 GaussianField))
    (hA : GaussianQuarticGoodIdeal a I)
    (hC : GaussianQuarticGoodIdeal c I) :
    GaussianQuarticGoodIdeal (a * c) I := by
  refine ⟨hA.1, ?_⟩
  intro P hPI
  refine ⟨(hA.2 P hPI).1, ?_⟩
  intro hmul
  rcases P.isPrime.mem_or_mem hmul with ha | hc
  · exact (hA.2 P hPI).2 ha
  · exact (hC.2 P hPI).2 hc

/-- The Gaussian quartic ideal symbol is multiplicative in its numerator. -/
theorem gaussianQuarticIdealSymbol_mul_numerator
    (a c : 𝓞 GaussianField) (I : Ideal (𝓞 GaussianField))
    (hA : GaussianQuarticGoodIdeal a I)
    (hC : GaussianQuarticGoodIdeal c I) :
    gaussianQuarticIdealSymbol (a * c) I
        (gaussianQuarticGoodIdeal_mul_numerator a c I hA hC) =
      gaussianQuarticIdealSymbol a I hA *
        gaussianQuarticIdealSymbol c I hC := by
  change idealPowerResidueSymbol GaussianField I hA.1 twoQuarticLevel
      twoPrimitiveFourthRoots (a * c)
      (fun P hP => (hA.2 P hP).1)
      (fun P hP => (gaussianQuarticGoodIdeal_mul_numerator a c I hA hC).2 P hP |>.2) =
    idealPowerResidueSymbol GaussianField I hA.1 twoQuarticLevel
      twoPrimitiveFourthRoots a
      (fun P hP => (hA.2 P hP).1)
      (fun P hP => (hA.2 P hP).2) *
    idealPowerResidueSymbol GaussianField I hC.1 twoQuarticLevel
      twoPrimitiveFourthRoots c
      (fun P hP => (hC.2 P hP).1)
      (fun P hP => (hC.2 P hP).2)
  exact
    (idealPowerResidueSymbol_mul GaussianField I hA.1 twoQuarticLevel
      twoPrimitiveFourthRoots a c
      (fun P hP => (hA.2 P hP).1)
      (fun P hP => (hA.2 P hP).2)
      (fun P hP => (hC.2 P hP).2))

private theorem gaussianSignedTwoPower_away
    (s : 𝓞 GaussianField) (hs : s = 1 ∨ s = -1) (k : ℕ)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField twoQuarticLevel) :
    s * (((2 : ℕ) : 𝓞 GaussianField) ^ k) ∉ P.asIdeal := by
  rcases hs with rfl | rfl
  · simpa only [one_mul] using gaussianTwoPower_away k P hP
  · simpa only [neg_one_mul] using gaussianNegativeTwoPower_away k P hP

private theorem gaussianSignedTwoPower_ne_zero
    (s : 𝓞 GaussianField) (hs : s = 1 ∨ s = -1) (k : ℕ) :
    s * (((2 : ℕ) : 𝓞 GaussianField) ^ k) ≠ 0 := by
  rcases hs with rfl | rfl <;> simp

/-- The odd numerator and the signed power of two combine under the
polynomial-size principal modulus `(64R)`. -/
theorem gaussianQuarticOddTimesSignedTwoPowerSymbol_eq_one
    (R : ℕ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (s : 𝓞 GaussianField) (hs : s = 1 ∨ s = -1) (k : ℕ)
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (hcong : b - 1 ∈ gaussianQuarticConductorCandidate R) :
    gaussianQuarticIdealSymbol
      ((R : 𝓞 GaussianField) * (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k)))
      (Ideal.span {b})
      (gaussianQuarticGoodIdeal_mul_numerator
        (R : 𝓞 GaussianField)
        (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k))
        (Ideal.span {b})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (R : 𝓞 GaussianField) b hb0
          (gaussianConductorCandidate_congruences R b hcong).2
          (gaussianConductorCandidate_congruences R b hcong).1)
        (gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
          (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k)) b hb0
          (gaussianSignedTwoPower_away s hs k)
          (gaussianConductorCandidate_congruences R b hcong).1)) = 1 := by
  let hodd := gaussianQuarticGoodIdeal_of_principal_congruences
    (R : 𝓞 GaussianField) b hb0
    (gaussianConductorCandidate_congruences R b hcong).2
    (gaussianConductorCandidate_congruences R b hcong).1
  let hdy := gaussianDyadicSupportedGoodIdeal_of_sixtyfour_congruence
    (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k)) b hb0
    (gaussianSignedTwoPower_away s hs k)
    (gaussianConductorCandidate_congruences R b hcong).1
  have hoddOne : gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
      (Ideal.span {b}) hodd = 1 :=
    gaussianQuarticIdealSymbol_eq_one_of_congruence R hR0 hRodd b hb0 hcong
  have hdyOne : gaussianQuarticIdealSymbol
      (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k))
      (Ideal.span {b}) hdy = 1 :=
    gaussianDyadicSupportedSymbol_eq_one_of_sixtyfour_congruence
      (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k)) b
      (gaussianSignedTwoPower_ne_zero s hs k) hb0
      (gaussianSignedTwoPower_away s hs k)
      (gaussianConductorCandidate_congruences R b hcong).1
  rw [gaussianQuarticIdealSymbol_mul_numerator
    (R : 𝓞 GaussianField)
    (s * (((2 : ℕ) : 𝓞 GaussianField) ^ k))
    (Ideal.span {b}) hodd hdy, hoddOne, hdyOne, one_mul]

end Erdos940.Quartic
