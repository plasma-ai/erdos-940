import Erdos940.Quartic.GaussianAnyIdealPrimeSum
import Erdos940.Quartic.GaussianConductor
import Erdos940.Quartic.GaussianFiniteCharacterNontrivial

/-!
# From a nontrivial admissible ideal symbol to a residue multiplier
-/

namespace Erdos940.Quartic.GaussianSymbolMultiplier

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries

/-- A Gaussian integer invertible modulo the rational modulus has unit
quadratic norm modulo that modulus. -/
private theorem gaussianNorm_isUnit_of_inverse_congruence
    (q : ℕ) (z t u : GaussianInt)
    (h : z * t - 1 = (q : GaussianInt) * u) :
    IsUnit ((z.re : ZMod q) ^ 2 + (z.im : ZMod q) ^ 2) := by
  have hmul : z * t = 1 + (q : GaussianInt) * u := by
    linear_combination h
  have hnorm : ((z.norm : ℤ) : ZMod q) *
      ((t.norm : ℤ) : ZMod q) = 1 := by
    rw [← Int.cast_mul, ← Zsqrtd.norm_mul, hmul]
    simp [Zsqrtd.norm_def, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_mul, Zsqrtd.im_mul]
  have hnormz : ((z.norm : ℤ) : ZMod q) =
      (z.re : ZMod q) ^ 2 + (z.im : ZMod q) ^ 2 := by
    simp [Zsqrtd.norm_def, pow_two]
  rw [← hnormz]
  exact isUnit_iff_exists_inv.mpr ⟨(t.norm : ZMod q), hnorm⟩

/-- Admissibility for a signed rational numerator gives an inverse of its
principal denominator generator modulo `64 |R|`. -/
theorem signedGoodIdeal_exists_inverse_modulus
    (R : ℤ) (hR0 : R ≠ 0)
    (b : 𝓞 GaussianField)
    (hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
      (Ideal.span {b})) :
    ∃ t : 𝓞 GaussianField,
      b * t - 1 ∈ Ideal.span {((64 * R.natAbs : ℕ) : 𝓞 GaussianField)} := by
  obtain ⟨N, hR | hR⟩ := R.eq_nat_or_neg
  · subst R
    have hN0 : N ≠ 0 := by exact_mod_cast hR0
    obtain ⟨t, _, ht⟩ := gaussianQuarticGoodIdeal_exists_inverse_candidate
      N hN0 b hgood
    exact ⟨t, by simpa [gaussianQuarticConductorCandidate] using ht⟩
  · subst R
    have hN0 : N ≠ 0 := by simpa using hR0
    have hgood' : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
        (Ideal.span {b}) :=
      (gaussianQuarticGoodIdeal_neg_iff (N : 𝓞 GaussianField)
        (Ideal.span {b})).mp (by simpa using hgood)
    obtain ⟨t, _, ht⟩ := gaussianQuarticGoodIdeal_exists_inverse_candidate
      N hN0 b hgood'
    exact ⟨t, by simpa [gaussianQuarticConductorCandidate] using ht⟩

/-- The lattice coordinates of an admissible principal denominator have
unit quadratic norm modulo the rational conductor. -/
theorem signedGoodIdeal_coordinates_norm_isUnit
    (R : ℤ) (hR0 : R ≠ 0)
    (b : 𝓞 GaussianField)
    (hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
      (Ideal.span {b})) :
    IsUnit (((gaussianFourthIntegerRingEquiv.symm b).re :
        ZMod (64 * R.natAbs)) ^ 2 +
      ((gaussianFourthIntegerRingEquiv.symm b).im :
        ZMod (64 * R.natAbs)) ^ 2) := by
  let q : ℕ := 64 * R.natAbs
  let z : GaussianInt := gaussianFourthIntegerRingEquiv.symm b
  obtain ⟨t, ht⟩ := signedGoodIdeal_exists_inverse_modulus R hR0 b hgood
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp ht
  let tZ : GaussianInt := gaussianFourthIntegerRingEquiv.symm t
  let uZ : GaussianInt := gaussianFourthIntegerRingEquiv.symm u
  have hring : z * tZ - 1 = (q : GaussianInt) * uZ := by
    apply gaussianFourthIntegerRingEquiv.injective
    simpa only [map_sub, map_mul, map_one, map_natCast,
      RingEquiv.apply_symm_apply, z, tZ, uZ, q] using hu
  exact gaussianNorm_isUnit_of_inverse_congruence q z tZ uZ hring

/-- A nontrivial quartic symbol on a good principal ideal supplies exactly
the admissible lattice multiplier needed for the zero-mean argument. -/
theorem exists_admissible_multiplier_of_symbol_witness
    (R : ℤ) (hR0 : R ≠ 0) (ι : GaussianField →+* ℂ)
    (b : 𝓞 GaussianField)
    (hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
      (Ideal.span {b}))
    (hsymbol : gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
      (Ideal.span {b}) hgood ≠ 1) :
    ∃ a : ℤ × ℤ,
      quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1 ∧
      IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
        (a.2 : ZMod (64 * R.natAbs)) ^ 2) := by
  let z : GaussianInt := gaussianFourthIntegerRingEquiv.symm b
  let a : ℤ × ℤ := (z.re, z.im)
  have hb : gaussianPointInteger a = b := by
    have hz : (⟨z.re, z.im⟩ : GaussianInt) = z := by ext <;> rfl
    change gaussianFourthIntegerRingEquiv (⟨z.re, z.im⟩ : GaussianInt) = b
    rw [hz]
    exact RingEquiv.apply_symm_apply _ _
  have hweight : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a =
      gaussianQuarticComplexValue ι
        (gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood) := by
    simp [quarticIdealLatticeWeight, hb, hgood]
  refine ⟨a, ?_, ?_⟩
  · rw [hweight]
    exact GaussianZeroMean.gaussianQuarticComplexValue_ne_one ι _ hsymbol
  · exact signedGoodIdeal_coordinates_norm_isUnit R hR0 b hgood

/-- The present nontriviality classification in the exact multiplier
interface required by the all-signed type-zero L-series bound. The dyadic
residual classes are recorded explicitly, rather than assumed away. -/
theorem signedInteger_multiplier_or_fourth_power_or_dyadic_residual
    (R : ℤ) (hR0 : R ≠ 0) (ι : GaussianField →+* ℂ) :
    (∃ a : ℤ × ℤ,
      quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1 ∧
      IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
        (a.2 : ZMod (64 * R.natAbs)) ^ 2)) ∨
      (∃ u : ℕ, R = (u : ℤ) ^ 4) ∨
      (∃ k u : ℕ, ¬ 4 ∣ k ∧
        (R = (2 : ℤ) ^ k * (u : ℤ) ^ 4 ∨
          R = -((2 : ℤ) ^ k * (u : ℤ) ^ 4))) := by
  rcases signedInteger_nontrivial_or_fourth_power_or_dyadic_residual
    R hR0 with ⟨b, hgood, hsymbol⟩ | hrest
  · exact Or.inl (exists_admissible_multiplier_of_symbol_witness
      R hR0 ι b hgood hsymbol)
  · exact Or.inr hrest

/-- Conductor classification as a multiplier alternative for the all-signed
type-zero Gaussian L-series estimate. -/
theorem signedInteger_multiplier_or_gaussian_fourth_power
    (R : ℤ) (hR0 : R ≠ 0) (ι : GaussianField →+* ℂ) :
    (∃ a : ℤ × ℤ,
      quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1 ∧
      IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
        (a.2 : ZMod (64 * R.natAbs)) ^ 2)) ∨
      (∃ v : 𝓞 GaussianField, v ^ 4 = (R : 𝓞 GaussianField)) := by
  rcases signedInteger_nontrivial_or_gaussian_fourth_power R hR0 with
    ⟨b, hgood, hsymbol⟩ | hfourth
  · exact Or.inl (exists_admissible_multiplier_of_symbol_witness
      R hR0 ι b hgood hsymbol)
  · exact Or.inr hfourth

end Erdos940.Quartic.GaussianSymbolMultiplier
