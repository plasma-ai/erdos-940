import Erdos940.Quartic.GaussianHeckeCharacters
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity
import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
import ClassFieldTheory.Theorems.HilbertSymbols.PowerClassEqOneIff
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# A congruence lemma for quartic symbols

The symbol in the opposite reciprocity direction is elementary: a numerator
congruent to one modulo the denominator has trivial quartic symbol. The
reciprocal symbol and the Hilbert factors at the primes above two determine
the conductor congruences.
-/

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols

namespace Erdos940.Quartic

attribute [local instance] Ideal.Quotient.field

noncomputable local instance conductorResidueFintype
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    Fintype (𝓞 GaussianField ⧸ P.asIdeal) :=
  Fintype.ofFinite _

private def conductorQuarticLevel : ℕ+ := ⟨4, by decide⟩

private theorem conductorPrimitiveFourthRoots :
    (primitiveRoots 4 GaussianField).Nonempty := by
  letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) ℚ GaussianField
      (Set.mem_singleton 4) (by decide : 4 ≠ 0)
  exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 4)).2 hζ⟩

/-- A prime whose ideal norm is prime to four does not lie above the
exponent ideal `(4)`. -/
private theorem gaussianPrime_away_from_exponent
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : (Ideal.absNorm P.asIdeal).Coprime 4) :
    P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField conductorQuarticLevel := by
  intro hbad
  have hdiv : P.asIdeal ∣ Ideal.span {((4 : ℕ) : 𝓞 GaussianField)} := by
    simpa [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
      GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal,
      conductorQuarticLevel] using hbad
  have hnormdvd : Ideal.absNorm P.asIdeal ∣
      4 ^ Module.finrank ℤ (𝓞 GaussianField) := by
    rw [← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdiv)
  have hcop : (Ideal.absNorm P.asIdeal).Coprime
      (4 ^ Module.finrank ℤ (𝓞 GaussianField)) :=
    hP.pow_right _
  have hnormone : Ideal.absNorm P.asIdeal = 1 := by
    exact (Nat.gcd_eq_left_iff_dvd.mpr hnormdvd).symm.trans hcop
  exact (Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top) hnormone

/-- A local fourth power in the second argument kills the finite Hilbert
factor. This is the target interface for the dyadic Hensel lemma. -/
private theorem gaussianFiniteHilbert_eq_one_of_local_fourth_power
    (v : HeightOneSpectrum (𝓞 GaussianField))
    (a b : GaussianFieldˣ)
    (hpow : ∃ u : (HeightOneSpectrum.adicAbv GaussianField v).Completionˣ,
      u ^ 4 = GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
        GaussianField v b) :
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
      GaussianField conductorQuarticLevel (by norm_num)
      conductorPrimitiveFourthRoots v a b = 1 := by
  let C := (HeightOneSpectrum.adicAbv GaussianField v).Completion
  letI : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  letI : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  have hlocal : LocalClassFieldTheory.Kummer.localHilbertSymbol
      C conductorQuarticLevel
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_natCast_ne_zero
        GaussianField conductorQuarticLevel (by norm_num) v)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty
        GaussianField conductorQuarticLevel conductorPrimitiveFourthRoots v)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
        GaussianField v a)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
        GaussianField v b) = 1 := by
    let hn := GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_natCast_ne_zero
      GaussianField conductorQuarticLevel (by norm_num) v
    let hmu := GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty
      GaussianField conductorQuarticLevel conductorPrimitiveFourthRoots v
    have hpowclass : ClassFieldTheory.powerClass C conductorQuarticLevel
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
          GaussianField v b) = 1 := by
      apply (ClassFieldTheory.powerClass_eq_one_iff C conductorQuarticLevel _).2
      obtain ⟨u, hu⟩ := hpow
      refine ⟨u, ?_⟩
      change u ^ 4 = _
      exact hu
    have hpair := ClassFieldTheory.localHilbertPairing_powerClass
      C conductorQuarticLevel hn hmu
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
        GaussianField v a)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
        GaussianField v b)
    rw [hpowclass, map_one] at hpair
    apply (KummerTheory.nthRootsSubgroupEquivRootsOfUnity C
      (conductorQuarticLevel : ℕ)).injective
    simpa only [ClassFieldTheory.localHilbertSymbol, map_one] using hpair.symm
  unfold GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
  apply (KummerTheory.nthRootsSubgroupEquivOfPrimitiveRoots GaussianField C
    conductorQuarticLevel conductorPrimitiveFourthRoots).injective
  rw [MulEquiv.apply_symm_apply, map_one]
  exact hlocal

/-- Convert a fourth root in the completion field into the unit-valued
fourth root expected by the local Hilbert-symbol API. -/
theorem gaussianLocalFourthRoot_to_unit
    (v : HeightOneSpectrum (𝓞 GaussianField))
    (b : 𝓞 GaussianField) (hb : b ≠ 0)
    (hroot : ∃ y : (HeightOneSpectrum.adicAbv GaussianField v).Completion,
      y ^ 4 = algebraMap GaussianField
        (HeightOneSpectrum.adicAbv GaussianField v).Completion (b : GaussianField)) :
    ∃ u : (HeightOneSpectrum.adicAbv GaussianField v).Completionˣ,
      u ^ 4 = GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
        GaussianField v
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit GaussianField b hb) := by
  let C := (HeightOneSpectrum.adicAbv GaussianField v).Completion
  obtain ⟨y, hy⟩ := hroot
  have hbField : (b : GaussianField) ≠ 0 := by
    intro hzero
    apply hb
    exact Subtype.ext hzero
  have hmap : algebraMap GaussianField C (b : GaussianField) ≠ 0 :=
    (algebraMap GaussianField C).injective.ne hbField
  have hy0 : y ≠ 0 := by
    intro hz
    apply hmap
    simpa [hz] using hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  change y ^ 4 = algebraMap GaussianField C (b : GaussianField)
  exact hy

/-- The global reciprocity correction is trivial if the second parameter
is a fourth power in every completion over the exponent four. -/
theorem gaussianCorrection_eq_one_of_local_fourth_powers
    (a b : GaussianFieldˣ)
    (hpow : ∀ v : HeightOneSpectrum (𝓞 GaussianField),
      v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField conductorQuarticLevel →
      ∃ u : (HeightOneSpectrum.adicAbv GaussianField v).Completionˣ,
        u ^ 4 = GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit
          GaussianField v b) :
    GlobalClassFieldTheory.Reciprocity.powerResidueBadPlaceCorrection
      GaussianField conductorQuarticLevel (by norm_num)
      conductorPrimitiveFourthRoots a b = 1 := by
  unfold GlobalClassFieldTheory.Reciprocity.powerResidueBadPlaceCorrection
  have hinf : (∏ v : InfinitePlace GaussianField,
      GlobalClassFieldTheory.Reciprocity.infinitePlaceHilbertSymbol
        GaussianField conductorQuarticLevel v a b) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    exact GlobalClassFieldTheory.Reciprocity.infinitePlaceHilbertSymbol_eq_one_of_ne_two
      GaussianField conductorQuarticLevel v a b (by decide)
  have hfin : (∏ v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField conductorQuarticLevel,
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        GaussianField conductorQuarticLevel (by norm_num)
        conductorPrimitiveFourthRoots v a b) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    exact gaussianFiniteHilbert_eq_one_of_local_fourth_power v a b (hpow v hv)
  rw [hinf, hfin, one_mul]

private theorem primeSymbol_eq_one_of_sub_one_mem
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) GaussianField).Nonempty)
    (a : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (ha : a ∉ P.asIdeal) (hcong : a - 1 ∈ P.asIdeal) :
    primeIdealPowerResidueSymbol GaussianField P n hmu h2 a ha = 1 := by
  apply (rootsOfUnityReductionEquiv GaussianField P n hmu h2).injective
  rw [rootsOfUnityReductionEquiv_primeIdealPowerResidueSymbol, map_one]
  apply (finiteFieldPowerResidueSymbol_eq_one_iff
    (𝓞 GaussianField ⧸ P.asIdeal) n _ _).2
  refine ⟨1, ?_⟩
  apply Units.ext
  have hq : Ideal.Quotient.mk P.asIdeal (a - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hcong
  have ha1 : Ideal.Quotient.mk P.asIdeal a = 1 := by
    exact sub_eq_zero.mp (by simpa using hq)
  simpa [primeIdealResidueUnit] using ha1.symm

/-- A Gaussian numerator equal to one modulo an admissible prime has
trivial quartic residue symbol at that prime. -/
theorem gaussianQuarticPrimeSymbol_eq_one_of_sub_one_mem
    (a : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (ha : a ∉ P.asIdeal) (hcong : a - 1 ∈ P.asIdeal) :
    gaussianQuarticPrimeSymbol a P h2 ha = 1 := by
  unfold gaussianQuarticPrimeSymbol
  exact primeSymbol_eq_one_of_sub_one_mem conductorQuarticLevel
    conductorPrimitiveFourthRoots a P h2 ha hcong

/-- A numerator congruent to one modulo an admissible denominator ideal
has trivial quartic ideal symbol. -/
theorem gaussianQuarticIdealSymbol_eq_one_of_sub_one_mem
    (a : 𝓞 GaussianField) (I : Ideal (𝓞 GaussianField))
    (hI : GaussianQuarticGoodIdeal a I) (hcong : a - 1 ∈ I) :
    gaussianQuarticIdealSymbol a I hI = 1 := by
  classical
  unfold gaussianQuarticIdealSymbol idealPowerResidueSymbol
  apply Finset.prod_eq_one
  intro P _
  have hPI : P.1.asIdeal ∣ I :=
    (mem_idealPrimeDivisors GaussianField I P.1).mp P.2
  have hcongP : a - 1 ∈ P.1.asIdeal :=
    (Ideal.dvd_iff_le.mp hPI) hcong
  change gaussianQuarticPrimeSymbol a P.1 (hI.2 P.1 hPI).1
      (hI.2 P.1 hPI).2 ^ idealPrimeMultiplicity GaussianField P.1 I = 1
  rw [gaussianQuarticPrimeSymbol_eq_one_of_sub_one_mem a P.1
    (hI.2 P.1 hPI).1 (hI.2 P.1 hPI).2 hcongP]
  exact one_pow _

theorem gaussianPrime_coprime_four_of_two_not_mem
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal) :
    (Ideal.absNorm P.asIdeal).Coprime 4 := by
  obtain ⟨p, n, hn, hpP, hp, hnorm⟩ :=
    Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    exact h2 hpP
  have hpc : p.Coprime 4 := by
    have hpc2 : p.Coprime 2 := hp.odd_of_ne_two hp2 |>.coprime_two_right
    simpa only [show (4 : ℕ) = 2 ^ 2 by decide] using hpc2.pow_right 2
  rw [hnorm]
  exact hpc.pow_left n

private theorem gaussianPrime_not_mem_of_congruent_one
    (b t : 𝓞 GaussianField)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hPb : P.asIdeal ∣ Ideal.span {b})
    (hcong : b - 1 ∈ Ideal.span {t}) :
    t ∉ P.asIdeal := by
  intro ht
  have hb : b ∈ P.asIdeal :=
    (Ideal.dvd_iff_le.mp hPb) (Ideal.mem_span_singleton_self b)
  have hbt : b - 1 ∈ P.asIdeal := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hcong
    rw [hc]
    exact P.asIdeal.mul_mem_right c ht
  have h1 : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
    convert P.asIdeal.sub_mem hb hbt using 1 <;> ring
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one P.asIdeal).mpr h1)

/-- A principal denominator congruent to one modulo both `a` and rational
`64` is admissible for the quartic symbol of `a`. -/
theorem gaussianQuarticGoodIdeal_of_principal_congruences
    (a b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (ha : b - 1 ∈ Ideal.span {a})
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    GaussianQuarticGoodIdeal a (Ideal.span {b}) := by
  refine ⟨by simpa [Ideal.span_singleton_eq_bot] using hb0, ?_⟩
  intro P hPb
  have haP : a ∉ P.asIdeal :=
    gaussianPrime_not_mem_of_congruent_one b a P hPb ha
  have h64P : ((64 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussianPrime_not_mem_of_congruent_one b _ P hPb h64
  have h2P : ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro h2
    apply h64P
    have hpow : (((2 : ℕ) : 𝓞 GaussianField) ^ 6) ∈ P.asIdeal :=
      (P.isPrime.pow_mem_iff_mem 6 (by decide)).2 h2
    convert hpow using 1 <;> norm_num
  exact ⟨gaussianPrime_coprime_four_of_two_not_mem P h2P, haP⟩

/-- Mutual admissibility of coprime principal parameters: if `b` avoids
every prime over `(a)` and is one modulo `64`, then `a` avoids every prime
over `(b)`. -/
theorem gaussianQuarticGoodIdeal_reciprocal_of_good_and_congruent_sixtyfour
    (a b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (hBA : GaussianQuarticGoodIdeal b (Ideal.span {a}))
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    GaussianQuarticGoodIdeal a (Ideal.span {b}) := by
  refine ⟨Ideal.span_singleton_eq_bot.not.mpr hb0, ?_⟩
  intro P hPb
  have h64P : ((64 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussianPrime_not_mem_of_congruent_one b _ P hPb h64
  have h2P : ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro h2
    apply h64P
    have hpow : (((2 : ℕ) : 𝓞 GaussianField) ^ 6) ∈ P.asIdeal :=
      (P.isPrime.pow_mem_iff_mem 6 (by decide)).2 h2
    convert hpow using 1 <;> norm_num
  have haP : a ∉ P.asIdeal := by
    intro ha
    have hPa : P.asIdeal ∣ Ideal.span {a} :=
      Ideal.dvd_span_singleton.mpr ha
    have hbnot := (hBA.2 P hPa).2
    have hb : b ∈ P.asIdeal :=
      (Ideal.dvd_iff_le.mp hPb) (Ideal.mem_span_singleton_self b)
    exact hbnot hb
  exact ⟨gaussianPrime_coprime_four_of_two_not_mem P h2P, haP⟩

/-- The reverse symbol appearing in reciprocity is admissible when the
original denominator is odd and the new numerator is one modulo it. -/
theorem gaussianQuarticGoodIdeal_reverse_of_odd_and_congruent
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0)
    (haOdd : a - 1 ∈ Ideal.span {((2 : ℕ) : 𝓞 GaussianField)})
    (hcong : b - 1 ∈ Ideal.span {a}) :
    GaussianQuarticGoodIdeal b (Ideal.span {a}) := by
  refine ⟨by simpa [Ideal.span_singleton_eq_bot] using ha0, ?_⟩
  intro P hPa
  have h2P : ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussianPrime_not_mem_of_congruent_one a _ P hPa haOdd
  have hbcong : b - 1 ∈ P.asIdeal :=
    (Ideal.dvd_iff_le.mp hPa) hcong
  have hbP : b ∉ P.asIdeal := by
    intro hb
    have h1 : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
      convert P.asIdeal.sub_mem hb hbcong using 1 <;> ring
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one P.asIdeal).mpr h1)
  exact ⟨gaussianPrime_coprime_four_of_two_not_mem P h2P, hbP⟩

/-- Every nonzero ideal factor of a quartic-admissible ideal remains
quartic-admissible. -/
theorem gaussianQuarticGoodIdeal_of_dvd
    (R : 𝓞 GaussianField) (I J : Ideal (𝓞 GaussianField))
    (hI : GaussianQuarticGoodIdeal R I) (hJ0 : J ≠ 0)
    (hJI : J ∣ I) : GaussianQuarticGoodIdeal R J := by
  exact ⟨hJ0, fun P hPJ => hI.2 P (dvd_trans hPJ hJI)⟩

/-- Reciprocity reduces the principal-ideal conductor assertion to its
explicit correction at the places above two. In particular, once that
correction is trivial, congruence to one modulo `(a)` kills the symbol
`(a/(b))`. -/
theorem gaussianQuarticPrincipalSymbol_eq_one_of_correction_eq_one
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hAB : GaussianQuarticGoodIdeal a (Ideal.span {b}))
    (hBA : GaussianQuarticGoodIdeal b (Ideal.span {a}))
    (hcong : b - 1 ∈ Ideal.span {a})
    (hCorrection :
      GlobalClassFieldTheory.Reciprocity.powerResidueBadPlaceCorrection
        GaussianField conductorQuarticLevel (by norm_num)
        conductorPrimitiveFourthRoots
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit
          GaussianField a ha0)
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit
          GaussianField b hb0) = 1) :
    gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB = 1 := by
  have hBAone : gaussianQuarticIdealSymbol b (Ideal.span {a}) hBA = 1 :=
    gaussianQuarticIdealSymbol_eq_one_of_sub_one_mem b _ hBA hcong
  have hRec :=
    GlobalClassFieldTheory.Reciprocity.idealPowerResidueSymbol_reciprocity_with_bad_place_correction
      GaussianField conductorQuarticLevel (by norm_num)
      conductorPrimitiveFourthRoots a b ha0 hb0
      (fun P hP => (hBA.2 P hP).1)
      (fun P hP => (hAB.2 P hP).1)
      (fun P hP => (hAB.2 P hP).2)
      (fun P hP => (hBA.2 P hP).2)
      (fun P hP => gaussianPrime_away_from_exponent P (hBA.2 P hP).1)
      (fun P hP => gaussianPrime_away_from_exponent P (hAB.2 P hP).1)
  change GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField 4 (gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB) =
    _ at hRec
  rw [hCorrection, inv_one, one_mul] at hRec
  change GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField 4 (gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB) =
    GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField 4 (gaussianQuarticIdealSymbol b (Ideal.span {a}) hBA) at hRec
  rw [hBAone] at hRec
  exact (GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots_injective
    GaussianField 4) hRec

/-- Principal congruence kills the quartic symbol once the second parameter
has a fourth root at all dyadic completions. -/
theorem gaussianQuarticPrincipalSymbol_eq_one_of_local_fourth_powers
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hAB : GaussianQuarticGoodIdeal a (Ideal.span {b}))
    (hBA : GaussianQuarticGoodIdeal b (Ideal.span {a}))
    (hcong : b - 1 ∈ Ideal.span {a})
    (hpow : ∀ v : HeightOneSpectrum (𝓞 GaussianField),
      v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField conductorQuarticLevel →
      ∃ y : (HeightOneSpectrum.adicAbv GaussianField v).Completion,
        y ^ 4 = algebraMap GaussianField
          (HeightOneSpectrum.adicAbv GaussianField v).Completion (b : GaussianField)) :
    gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB = 1 := by
  apply gaussianQuarticPrincipalSymbol_eq_one_of_correction_eq_one
    a b ha0 hb0 hAB hBA hcong
  apply gaussianCorrection_eq_one_of_local_fourth_powers
  intro v hv
  exact gaussianLocalFourthRoot_to_unit v b hb0 (hpow v hv)

/-- Quartic reciprocity with the dyadic correction discharged by local
fourth roots of the second parameter. Unlike the conductor corollary, this
does not assume either reciprocal symbol is trivial. -/
theorem gaussianQuarticIdealSymbol_reciprocity_of_local_fourth_powers
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hAB : GaussianQuarticGoodIdeal a (Ideal.span {b}))
    (hBA : GaussianQuarticGoodIdeal b (Ideal.span {a}))
    (hpow : ∀ v : HeightOneSpectrum (𝓞 GaussianField),
      v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField conductorQuarticLevel →
      ∃ y : (HeightOneSpectrum.adicAbv GaussianField v).Completion,
        y ^ 4 = algebraMap GaussianField
          (HeightOneSpectrum.adicAbv GaussianField v).Completion (b : GaussianField)) :
    gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB =
      gaussianQuarticIdealSymbol b (Ideal.span {a}) hBA := by
  have hCorrection :
      GlobalClassFieldTheory.Reciprocity.powerResidueBadPlaceCorrection
        GaussianField conductorQuarticLevel (by norm_num)
        conductorPrimitiveFourthRoots
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit
          GaussianField a ha0)
        (GlobalClassFieldTheory.Reciprocity.nonzeroIntegralFieldUnit
          GaussianField b hb0) = 1 := by
    apply gaussianCorrection_eq_one_of_local_fourth_powers
    intro v hv
    exact gaussianLocalFourthRoot_to_unit v b hb0 (hpow v hv)
  have hRec :=
    GlobalClassFieldTheory.Reciprocity.idealPowerResidueSymbol_reciprocity_with_bad_place_correction
      GaussianField conductorQuarticLevel (by norm_num)
      conductorPrimitiveFourthRoots a b ha0 hb0
      (fun P hP => (hBA.2 P hP).1)
      (fun P hP => (hAB.2 P hP).1)
      (fun P hP => (hAB.2 P hP).2)
      (fun P hP => (hBA.2 P hP).2)
      (fun P hP => gaussianPrime_away_from_exponent P (hBA.2 P hP).1)
      (fun P hP => gaussianPrime_away_from_exponent P (hAB.2 P hP).1)
  change GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField 4 (gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB) =
    _ at hRec
  rw [hCorrection, inv_one, one_mul] at hRec
  change GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField 4 (gaussianQuarticIdealSymbol a (Ideal.span {b}) hAB) =
    GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots
      GaussianField 4 (gaussianQuarticIdealSymbol b (Ideal.span {a}) hBA) at hRec
  exact (GlobalClassFieldTheory.Reciprocity.integralRootsOfUnityToNthRoots_injective
    GaussianField 4) hRec

/-- A convenient explicit modulus candidate for a rational quartic parameter.
The assertion that the quartic ideal symbol factors through this modulus is
separate from its norm calculation. -/
noncomputable def gaussianQuarticConductorCandidate (R : ℕ) : Ideal (𝓞 GaussianField) :=
  Ideal.span {((64 * R : ℕ) : 𝓞 GaussianField)}

/-- Congruence modulo `(64R)` gives both congruences needed in the
reciprocity argument. -/
theorem gaussianConductorCandidate_congruences (R : ℕ)
    (b : 𝓞 GaussianField)
    (h : b - 1 ∈ gaussianQuarticConductorCandidate R) :
    b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} ∧
      b - 1 ∈ Ideal.span {((R : ℕ) : 𝓞 GaussianField)} := by
  rcases (Ideal.mem_span_singleton.mp h) with ⟨c, hc⟩
  constructor
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨(R : 𝓞 GaussianField) * c, ?_⟩
    simpa [gaussianQuarticConductorCandidate, Nat.cast_mul,
      mul_assoc, mul_comm, mul_left_comm] using hc
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨(64 : 𝓞 GaussianField) * c, ?_⟩
    simpa [gaussianQuarticConductorCandidate, Nat.cast_mul,
      mul_assoc, mul_comm, mul_left_comm] using hc

/-- At a place over four, congruence to one modulo rational 64 is strictly
closer than the square of the local norm of four. This is the quantitative
Hensel hypothesis for `X^4-b` at the approximate root one. -/
theorem gaussianDyadic_norm_sub_one_lt_norm_four_sq
    (v : HeightOneSpectrum (𝓞 GaussianField))
    (hv : v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField conductorQuarticLevel)
    (b : 𝓞 GaussianField)
    (hb : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    let C := (HeightOneSpectrum.adicAbv GaussianField v).Completion
    ‖algebraMap GaussianField C (b : GaussianField) - 1‖ < ‖(4 : C)‖ ^ 2 := by
  let C := (HeightOneSpectrum.adicAbv GaussianField v).Completion
  have hdiv : v.asIdeal ∣ Ideal.span {((4 : ℕ) : 𝓞 GaussianField)} := by
    simpa [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
      GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal,
      conductorQuarticLevel] using hv
  have h4mem : ((4 : ℕ) : 𝓞 GaussianField) ∈ v.asIdeal := by
    rwa [Ideal.dvd_span_singleton] at hdiv
  have h4lt : ‖(4 : C)‖ < 1 := by
    have h := (v.adicAbv_coe_lt_one_iff (K := GaussianField)
      (HeightOneSpectrum.one_lt_absNorm_nnreal v)
      ((4 : ℕ) : 𝓞 GaussianField)).2 h4mem
    have h4cast : (4 : C) = algebraMap GaussianField C
        (((4 : ℕ) : 𝓞 GaussianField) : GaussianField) := by simp [map_ofNat]
    calc
      ‖(4 : C)‖ = ‖algebraMap GaussianField C
          (((4 : ℕ) : 𝓞 GaussianField) : GaussianField)‖ := congrArg norm h4cast
      _ = HeightOneSpectrum.adicAbv GaussianField v
          (((4 : ℕ) : 𝓞 GaussianField) : GaussianField) :=
        AbsoluteValue.completionAbsoluteValue_coe _ _
      _ < 1 := h
  have h4ne : (4 : C) ≠ 0 :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_natCast_ne_zero
      GaussianField conductorQuarticLevel (by norm_num) v
  have h4pos : 0 < ‖(4 : C)‖ := norm_pos_iff.mpr h4ne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hcNorm : ‖algebraMap GaussianField C (c : GaussianField)‖ ≤ 1 := by
    calc
      ‖algebraMap GaussianField C (c : GaussianField)‖ =
          HeightOneSpectrum.adicAbv GaussianField v (c : GaussianField) :=
        AbsoluteValue.completionAbsoluteValue_coe _ _
      _ ≤ 1 :=
        v.adicAbv_coe_le_one (K := GaussianField)
          (HeightOneSpectrum.one_lt_absNorm_nnreal v) c
  have hmap : algebraMap GaussianField C (b : GaussianField) - 1 =
      (64 : C) * algebraMap GaussianField C (c : GaussianField) := by
    have hcK : (b : GaussianField) - 1 =
        (64 : GaussianField) * (c : GaussianField) := by
      have h := congrArg (algebraMap (𝓞 GaussianField) GaussianField) hc
      simpa [NumberField.RingOfIntegers.coe_eq_algebraMap, map_ofNat] using h
    calc
      algebraMap GaussianField C (b : GaussianField) - 1 =
          algebraMap GaussianField C ((b : GaussianField) - 1) := by simp
      _ = algebraMap GaussianField C ((64 : GaussianField) * (c : GaussianField)) :=
        congrArg _ hcK
      _ = (64 : C) * algebraMap GaussianField C (c : GaussianField) := by
        simp [map_ofNat]
  have h64 : ‖(64 : C)‖ = ‖(4 : C)‖ ^ 3 := by
    convert norm_pow (4 : C) 3 using 1 <;> norm_num
  change ‖algebraMap GaussianField C (b : GaussianField) - 1‖ < ‖(4 : C)‖ ^ 2
  rw [hmap, norm_mul, h64]
  calc
    ‖(4 : C)‖ ^ 3 * ‖algebraMap GaussianField C (c : GaussianField)‖ ≤
        ‖(4 : C)‖ ^ 3 * 1 := by
      gcongr
    _ = ‖(4 : C)‖ ^ 3 := mul_one _
    _ < ‖(4 : C)‖ ^ 2 := by
      calc
        ‖(4 : C)‖ ^ 3 = ‖(4 : C)‖ * ‖(4 : C)‖ ^ 2 := by ring
        _ < 1 * ‖(4 : C)‖ ^ 2 :=
          mul_lt_mul_of_pos_right h4lt (pow_pos h4pos _)
        _ = ‖(4 : C)‖ ^ 2 := one_mul _
private theorem gaussianRingOfIntegers_rank_two :
    Module.finrank ℤ (𝓞 GaussianField) = 2 := by
  rw [NumberField.RingOfIntegers.rank]
  letI : NeZero (4 : ℕ) := ⟨by decide⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  rw [IsCyclotomicExtension.Rat.finrank 4 GaussianField]
  decide

/-- The explicit candidate has quadratic norm in the rational parameter. -/
theorem gaussianQuarticConductorCandidate_absNorm (R : ℕ) :
    Ideal.absNorm (gaussianQuarticConductorCandidate R) =
      (64 * R) ^ 2 := by
  unfold gaussianQuarticConductorCandidate
  rw [Ideal.absNorm_span_natCast, gaussianRingOfIntegers_rank_two]

/-- An element congruent to one modulo rational `64` cannot vanish. -/
theorem gaussian_ne_zero_of_sub_one_mem_sixtyfour
    (b : 𝓞 GaussianField)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) : b ≠ 0 := by
  intro hb0
  have hneg : (-1 : 𝓞 GaussianField) ∈
      Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} := by
    simpa [hb0] using h64
  have htop : Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} = ⊤ := by
    apply (Ideal.eq_top_iff_one _).2
    simpa using (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}).neg_mem hneg
  have hnorm : Ideal.absNorm (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) = 1 :=
    (Ideal.absNorm_eq_one_iff).2 htop
  rw [Ideal.absNorm_span_natCast, gaussianRingOfIntegers_rank_two] at hnorm
  norm_num at hnorm

/-- The principal congruence subgroup of the polynomial-size candidate
annihilates the quartic ideal symbol, provided the dyadic fourth-root
condition holds. This is the purely reciprocity-theoretic part of the
conductor theorem. -/
theorem gaussianQuarticIdealSymbol_eq_one_of_candidate_congruence
    (R : ℕ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (hcong : b - 1 ∈ gaussianQuarticConductorCandidate R)
    (hpow : ∀ v : HeightOneSpectrum (𝓞 GaussianField),
      v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField conductorQuarticLevel →
      ∃ y : (HeightOneSpectrum.adicAbv GaussianField v).Completion,
        y ^ 4 = algebraMap GaussianField
          (HeightOneSpectrum.adicAbv GaussianField v).Completion (b : GaussianField)) :
    gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {b})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (R : 𝓞 GaussianField) b hb0
          (gaussianConductorCandidate_congruences R b hcong).2
          (gaussianConductorCandidate_congruences R b hcong).1) = 1 := by
  have hRcast0 : (R : 𝓞 GaussianField) ≠ 0 := by
    exact_mod_cast hR0
  have hOdd : (R : 𝓞 GaussianField) - 1 ∈
      Ideal.span {((2 : ℕ) : 𝓞 GaussianField)} := by
    obtain ⟨k, hk⟩ := hRodd
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(k : 𝓞 GaussianField), ?_⟩
    push_cast
    rw [hk]
    push_cast
    ring
  have hrev : GaussianQuarticGoodIdeal b
      (Ideal.span {(R : 𝓞 GaussianField)}) :=
    gaussianQuarticGoodIdeal_reverse_of_odd_and_congruent
      (R : 𝓞 GaussianField) b hRcast0 hOdd
      (gaussianConductorCandidate_congruences R b hcong).2
  exact gaussianQuarticPrincipalSymbol_eq_one_of_local_fourth_powers
    (R : 𝓞 GaussianField) b hRcast0 hb0
    (gaussianQuarticGoodIdeal_of_principal_congruences
      (R : 𝓞 GaussianField) b hb0
      (gaussianConductorCandidate_congruences R b hcong).2
      (gaussianConductorCandidate_congruences R b hcong).1)
    hrev (gaussianConductorCandidate_congruences R b hcong).2 hpow

/-- Congruent principal generators have the same quartic symbol once an
inverse of one generator modulo the candidate conductor is supplied. The
triviality of the principal congruence subgroup is passed as a hypothesis so
the dyadic fourth-root theorem can be connected in a downstream module. -/
theorem gaussianQuarticIdealSymbol_congruent_of_inverse
    (R : ℕ) (b c t : 𝓞 GaussianField) (ht0 : t ≠ 0)
    (hB : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {b}))
    (hC : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {c}))
    (hbc : b - c ∈ gaussianQuarticConductorCandidate R)
    (hct : c * t - 1 ∈ gaussianQuarticConductorCandidate R)
    (htriv : ∀ d : 𝓞 GaussianField, ∀ hd0 : d ≠ 0,
      ∀ hd : d - 1 ∈ gaussianQuarticConductorCandidate R,
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {d})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (R : 𝓞 GaussianField) d hd0
          (gaussianConductorCandidate_congruences R d hd).2
          (gaussianConductorCandidate_congruences R d hd).1) = 1) :
    gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {b}) hB =
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {c}) hC := by
  have hctGood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
      (Ideal.span {c * t}) :=
    gaussianQuarticGoodIdeal_of_principal_congruences _ _
      (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mp hC.1) ht0)
      (gaussianConductorCandidate_congruences R (c * t) hct).2
      (gaussianConductorCandidate_congruences R (c * t) hct).1
  have htGood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
      (Ideal.span {t}) := by
    apply gaussianQuarticGoodIdeal_of_dvd _ _ _ hctGood
      (Ideal.span_singleton_eq_bot.not.mpr ht0)
    apply Ideal.dvd_span_singleton.mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨c, mul_comm c t⟩
  have hbt : b * t - 1 ∈ gaussianQuarticConductorCandidate R := by
    have hdiff : (b - c) * t ∈ gaussianQuarticConductorCandidate R :=
      (gaussianQuarticConductorCandidate R).mul_mem_right t hbc
    convert (gaussianQuarticConductorCandidate R).add_mem hdiff hct using 1 <;> ring
  have hb0 : b ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hB.1
  have hc0 : c ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hC.1
  have hBmul :
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
        (Ideal.span {b} * Ideal.span {t})
        (gaussianQuarticGoodIdeal_mul _ (Ideal.span {b}) (Ideal.span {t}) hB htGood) =
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {b}) hB *
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {t}) htGood := by
    exact gaussianQuarticIdealSymbol_mul (R : 𝓞 GaussianField)
      (Ideal.span {b}) (Ideal.span {t}) hB htGood
  have hCmul :
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
        (Ideal.span {c} * Ideal.span {t})
        (gaussianQuarticGoodIdeal_mul _ (Ideal.span {c}) (Ideal.span {t}) hC htGood) =
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {c}) hC *
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {t}) htGood := by
    exact gaussianQuarticIdealSymbol_mul (R : 𝓞 GaussianField)
      (Ideal.span {c}) (Ideal.span {t}) hC htGood
  have hBtriv :
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {b}) hB *
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {t}) htGood = 1 := by
    rw [← hBmul]
    simpa only [Ideal.span_singleton_mul_span_singleton] using
      htriv (b * t) (mul_ne_zero hb0 ht0) hbt
  have hCtriv :
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {c}) hC *
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {t}) htGood = 1 := by
    rw [← hCmul]
    simpa only [Ideal.span_singleton_mul_span_singleton] using
      htriv (c * t) (mul_ne_zero hc0 ht0) hct
  exact mul_right_cancel (hBtriv.trans hCtriv.symm)

/-- A quartic-admissible principal ideal is comaximal with the candidate
conductor `(64R)`. -/
theorem gaussianQuarticGoodIdeal_isCoprime_candidate
    (R : ℕ) (hR0 : R ≠ 0) (c : 𝓞 GaussianField)
    (hC : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {c})) :
    IsCoprime (Ideal.span {c}) (gaussianQuarticConductorCandidate R) := by
  have hq0 : gaussianQuarticConductorCandidate R ≠ ⊥ := by
    unfold gaussianQuarticConductorCandidate
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact_mod_cast (by omega : 64 * R ≠ 0)
  apply Ideal.coprime_of_no_prime_ge
  intro P hcP hqP hP
  have hP0 : P ≠ ⊥ := by
    intro hzero
    apply hq0
    exact bot_unique (by simpa [hzero] using hqP)
  let v : HeightOneSpectrum (𝓞 GaussianField) :=
    HeightOneSpectrum.ofPrime (Ideal.prime_of_isPrime hP0 hP)
  have hPc : v.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.mpr hcP
  have hgood := hC.2 v hPc
  have hqmem : ((64 * R : ℕ) : 𝓞 GaussianField) ∈ v.asIdeal :=
    hqP (Ideal.mem_span_singleton_self _)
  have hqprod : ((64 : ℕ) : 𝓞 GaussianField) *
      ((R : ℕ) : 𝓞 GaussianField) ∈ v.asIdeal := by
    simpa only [← Nat.cast_mul] using hqmem
  rcases v.isPrime.mem_or_mem hqprod with h64 | hR
  · have h4 : ((4 : ℕ) : 𝓞 GaussianField) ∈ v.asIdeal := by
      have h4cube : (((4 : ℕ) : 𝓞 GaussianField) ^ 3) ∈ v.asIdeal := by
        convert h64 using 1 <;> norm_num
      exact (v.isPrime.pow_mem_iff_mem 3 (by decide)).mp h4cube
    apply gaussianPrime_away_from_exponent v hgood.1
    have hdiv : v.asIdeal ∣ Ideal.span {((4 : ℕ) : 𝓞 GaussianField)} :=
      Ideal.dvd_span_singleton.mpr h4
    simpa [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
      GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal,
      conductorQuarticLevel] using hdiv
  · exact hgood.2 hR

/-- An admissible Gaussian integer has a nonzero inverse lift modulo
`(64R)`. -/
theorem gaussianQuarticGoodIdeal_exists_inverse_candidate
    (R : ℕ) (hR0 : R ≠ 0) (c : 𝓞 GaussianField)
    (hC : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {c})) :
    ∃ t : 𝓞 GaussianField, t ≠ 0 ∧
      c * t - 1 ∈ gaussianQuarticConductorCandidate R := by
  have hcop := gaussianQuarticGoodIdeal_isCoprime_candidate R hR0 c hC
  obtain ⟨i, hi, j, hj, hij⟩ := hcop.exists
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hi
  have hct : c * t - 1 ∈ gaussianQuarticConductorCandidate R := by
    have heq : c * t - 1 = -j := by
      rw [← ht]
      linear_combination hij
    rw [heq]
    exact (gaussianQuarticConductorCandidate R).neg_mem hj
  have hqtop : gaussianQuarticConductorCandidate R ≠ ⊤ := by
    intro htop
    have hnorm : Ideal.absNorm (gaussianQuarticConductorCandidate R) = 1 :=
      (Ideal.absNorm_eq_one_iff).2 htop
    rw [gaussianQuarticConductorCandidate_absNorm] at hnorm
    have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
    have hlarge : 64 ≤ 64 * R := by omega
    nlinarith
  refine ⟨t, ?_, hct⟩
  intro ht0
  have hneg : (-1 : 𝓞 GaussianField) ∈ gaussianQuarticConductorCandidate R := by
    simpa [ht0] using hct
  have h1 : (1 : 𝓞 GaussianField) ∈ gaussianQuarticConductorCandidate R := by
    simpa using (gaussianQuarticConductorCandidate R).neg_mem hneg
  exact hqtop ((Ideal.eq_top_iff_one _).mpr h1)

/-- Periodicity of the admissible principal-ideal symbol, conditional only on
triviality on the principal congruence subgroup. -/
theorem gaussianQuarticIdealSymbol_congruent
    (R : ℕ) (hR0 : R ≠ 0) (b c : 𝓞 GaussianField)
    (hB : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {b}))
    (hC : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {c}))
    (hbc : b - c ∈ gaussianQuarticConductorCandidate R)
    (htriv : ∀ d : 𝓞 GaussianField, ∀ hd0 : d ≠ 0,
      ∀ hd : d - 1 ∈ gaussianQuarticConductorCandidate R,
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {d})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (R : 𝓞 GaussianField) d hd0
          (gaussianConductorCandidate_congruences R d hd).2
          (gaussianConductorCandidate_congruences R d hd).1) = 1) :
    gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {b}) hB =
      gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {c}) hC := by
  obtain ⟨t, ht0, hct⟩ :=
    gaussianQuarticGoodIdeal_exists_inverse_candidate R hR0 c hC
  exact gaussianQuarticIdealSymbol_congruent_of_inverse
    R b c t ht0 hB hC hbc hct htriv

/-- A signed rational parameter uses the same congruence modulus. -/
noncomputable def gaussianQuarticSignedConductorCandidate (R : ℤ) :
    Ideal (𝓞 GaussianField) :=
  Ideal.span {((64 * R : ℤ) : 𝓞 GaussianField)}

/-- The signed conductor congruence implies the two component congruences. -/
theorem gaussianSignedConductorCandidate_congruences (R : ℤ)
    (b : 𝓞 GaussianField)
    (h : b - 1 ∈ gaussianQuarticSignedConductorCandidate R) :
    b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} ∧
      b - 1 ∈ Ideal.span {(R : 𝓞 GaussianField)} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h
  constructor
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨(R : 𝓞 GaussianField) * c, ?_⟩
    simpa [gaussianQuarticSignedConductorCandidate, Int.cast_mul,
      mul_assoc, mul_comm, mul_left_comm] using hc
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨(64 : 𝓞 GaussianField) * c, ?_⟩
    simpa [gaussianQuarticSignedConductorCandidate, Int.cast_mul,
      mul_assoc, mul_comm, mul_left_comm] using hc

/-- The reciprocity bridge for any nonzero odd signed rational parameter.
Only the dyadic fourth-root assertion remains to be supplied downstream. -/
theorem gaussianQuarticIdealSymbol_eq_one_of_signed_congruence
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (hcong : b - 1 ∈ gaussianQuarticSignedConductorCandidate R)
    (hpow : ∀ v : HeightOneSpectrum (𝓞 GaussianField),
      v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
        GaussianField conductorQuarticLevel →
      ∃ y : (HeightOneSpectrum.adicAbv GaussianField v).Completion,
        y ^ 4 = algebraMap GaussianField
          (HeightOneSpectrum.adicAbv GaussianField v).Completion (b : GaussianField)) :
    gaussianQuarticIdealSymbol (R : 𝓞 GaussianField) (Ideal.span {b})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (R : 𝓞 GaussianField) b hb0
          (gaussianSignedConductorCandidate_congruences R b hcong).2
          (gaussianSignedConductorCandidate_congruences R b hcong).1) = 1 := by
  have hRcast0 : (R : 𝓞 GaussianField) ≠ 0 := by
    exact_mod_cast hR0
  have hOdd : (R : 𝓞 GaussianField) - 1 ∈
      Ideal.span {((2 : ℕ) : 𝓞 GaussianField)} := by
    obtain ⟨k, hk⟩ := hRodd
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(k : 𝓞 GaussianField), ?_⟩
    push_cast
    rw [hk]
    push_cast
    ring
  have hrev : GaussianQuarticGoodIdeal b
      (Ideal.span {(R : 𝓞 GaussianField)}) :=
    gaussianQuarticGoodIdeal_reverse_of_odd_and_congruent
      (R : 𝓞 GaussianField) b hRcast0 hOdd
      (gaussianSignedConductorCandidate_congruences R b hcong).2
  exact gaussianQuarticPrincipalSymbol_eq_one_of_local_fourth_powers
    (R : 𝓞 GaussianField) b hRcast0 hb0
    (gaussianQuarticGoodIdeal_of_principal_congruences
      (R : 𝓞 GaussianField) b hb0
      (gaussianSignedConductorCandidate_congruences R b hcong).2
      (gaussianSignedConductorCandidate_congruences R b hcong).1)
    hrev (gaussianSignedConductorCandidate_congruences R b hcong).2 hpow

private theorem gaussianQuarticConductorCandidate_ne_top
    (R : ℕ) (hR0 : R ≠ 0) :
    gaussianQuarticConductorCandidate R ≠ ⊤ := by
  intro htop
  have hnorm : Ideal.absNorm (gaussianQuarticConductorCandidate R) = 1 :=
    (Ideal.absNorm_eq_one_iff).2 htop
  rw [gaussianQuarticConductorCandidate_absNorm] at hnorm
  have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
  have hlarge : 64 ≤ 64 * R := by omega
  nlinarith

private theorem gaussianPrime_two_not_mem_of_coprime_four
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : (Ideal.absNorm P.asIdeal).Coprime 4) :
    ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal := by
  intro h2
  have h4 : ((4 : ℕ) : 𝓞 GaussianField) ∈ P.asIdeal := by
    have h2sq : (((2 : ℕ) : 𝓞 GaussianField) ^ 2) ∈ P.asIdeal :=
      (P.isPrime.pow_mem_iff_mem 2 (by decide)).2 h2
    convert h2sq using 1 <;> norm_num
  apply gaussianPrime_away_from_exponent P hP
  have hdiv : P.asIdeal ∣ Ideal.span {((4 : ℕ) : 𝓞 GaussianField)} :=
    Ideal.dvd_span_singleton.mpr h4
  simpa [GlobalClassFieldTheory.Reciprocity.mem_powerResidueExponentFinitePlaces_iff,
    GlobalClassFieldTheory.Reciprocity.powerResidueExponentIdeal,
    conductorQuarticLevel] using hdiv

/-- Admissibility is invariant under congruence modulo the conductor
candidate. -/
theorem gaussianQuarticGoodIdeal_congruent
    (R : ℕ) (hR0 : R ≠ 0) (b c : 𝓞 GaussianField)
    (hC : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {c}))
    (hbc : b - c ∈ gaussianQuarticConductorCandidate R) :
    GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {b}) := by
  have hcop := gaussianQuarticGoodIdeal_isCoprime_candidate R hR0 c hC
  have hb0 : b ≠ 0 := by
    intro hb
    have hcq : c ∈ gaussianQuarticConductorCandidate R := by
      have hneg : -c ∈ gaussianQuarticConductorCandidate R := by
        simpa [hb] using hbc
      simpa using (gaussianQuarticConductorCandidate R).neg_mem hneg
    have hle : Ideal.span {c} ≤ gaussianQuarticConductorCandidate R :=
      (Ideal.span_singleton_le_iff_mem (I := gaussianQuarticConductorCandidate R)).mpr hcq
    have htop : gaussianQuarticConductorCandidate R = ⊤ := by
      have hsup := hcop.sup_eq
      rw [sup_eq_right.mpr hle] at hsup
      exact hsup
    exact gaussianQuarticConductorCandidate_ne_top R hR0 htop
  refine ⟨Ideal.span_singleton_eq_bot.not.mpr hb0, ?_⟩
  intro P hPb
  have htransfer (hq : ((64 * R : ℕ) : 𝓞 GaussianField) ∈ P.asIdeal) :
      P.asIdeal ∣ Ideal.span {c} := by
    have hqdiv : P.asIdeal ∣ gaussianQuarticConductorCandidate R := by
      exact Ideal.dvd_span_singleton.mpr hq
    have hdiff : b - c ∈ P.asIdeal :=
      (Ideal.dvd_iff_le.mp hqdiv) hbc
    have hb : b ∈ P.asIdeal :=
      (Ideal.dvd_iff_le.mp hPb) (Ideal.mem_span_singleton_self _)
    have hc : c ∈ P.asIdeal := by
      convert P.asIdeal.sub_mem hb hdiff using 1 <;> ring
    exact Ideal.dvd_span_singleton.mpr hc
  have hRnot : (R : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro hR
    have hq : ((64 * R : ℕ) : 𝓞 GaussianField) ∈ P.asIdeal := by
      convert P.asIdeal.mul_mem_left (64 : 𝓞 GaussianField) hR using 1 <;>
        norm_num [Nat.cast_mul]
    exact (hC.2 P (htransfer hq)).2 hR
  have h2not : ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro h2
    have h64 : ((64 : ℕ) : 𝓞 GaussianField) ∈ P.asIdeal := by
      have hpow : (((2 : ℕ) : 𝓞 GaussianField) ^ 6) ∈ P.asIdeal :=
        (P.isPrime.pow_mem_iff_mem 6 (by decide)).2 h2
      convert hpow using 1 <;> norm_num
    have hq : ((64 * R : ℕ) : 𝓞 GaussianField) ∈ P.asIdeal := by
      simpa only [Nat.cast_mul] using P.asIdeal.mul_mem_right (R : 𝓞 GaussianField) h64
    exact gaussianPrime_two_not_mem_of_coprime_four P
      (hC.2 P (htransfer hq)).1 h2
  exact ⟨gaussianPrime_coprime_four_of_two_not_mem P h2not, hRnot⟩

end Erdos940.Quartic
