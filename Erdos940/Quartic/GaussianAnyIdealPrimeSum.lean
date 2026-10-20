import Erdos940.Quartic.GaussianIdealEulerUniversal
import Erdos940.Quartic.GaussianIdealEulerIdentityLimit
import Erdos940.Quartic.GaussianAnyConductorPeriodicity
import Erdos940.Quartic.UniformEulerMajorant

/-!
# The type-zero Gaussian prime sum for all nonzero signed radicands

The ideal Euler product is proved from prime-ideal factorization.
Mean zero follows from one explicit admissible nontrivial multiplier;
periodicity holds for all nonzero signed rational parameters.
-/

namespace Erdos940.Quartic.GaussianAnyIdealPrimeSum

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianIdealEulerUniversal
open Erdos940.Quartic.GaussianIdealEulerIdentityLimit

theorem anySignedIdealPrimeSum_le_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (R : ℤ) (hR0 : R ≠ 0) (ι : GaussianField →+* ℂ)
    (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (B : ℝ) (hB : 2 ≤ B) (hlogB : 1 ≤ Real.log B)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ)) :
    (∑ P ∈ S,
      (quarticIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re /
        (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * ((64 * R.natAbs : ℕ) : ℝ) ^ 2)) +
        (Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + reciprocalSquareConstant) := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  let σ : ℝ := 1 + 1 / Real.log B
  have hlogpos : 0 < Real.log B := by linarith
  have hσ₁ : 1 < σ := by
    dsimp [σ]
    have hrecip : 0 < 1 / Real.log B := by positivity
    linarith
  have hσ₂ : σ ≤ 2 := by
    dsimp [σ]
    have hrecip : 1 / Real.log B ≤ 1 :=
      (div_le_iff₀ hlogpos).2 (by simpa using hlogB)
    linarith
  have hEulerIdentity : Complex.exp
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - gaussianPrimeTerm
          (quarticIdealWeight (R : 𝓞 GaussianField) ι) B P)) =
      LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι)
        (σ : ℂ) := by
    simpa only [σ, gaussianPrimeTerm_eq_weightedIdealTerm] using
      quartic_exp_prime_log_eq_LSeries
        (R : 𝓞 GaussianField) ι σ hσ₁
  have hperiod := quarticIdealLatticeWeight_any_signed_periodic R hR0 ι
  have hmean := GaussianZeroMean.residue_sum_zero_of_isUnit_norm_multiplier
    (64 * R.natAbs) (R : 𝓞 GaussianField) ι hperiod a ha hunit
  have hLpos : 0 <
      ‖LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖ := by
    dsimp [σ]
    rw [← hEulerIdentity]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hc (P : HeightOneSpectrum (𝓞 GaussianField)) :
      |(quarticIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans
      (norm_quarticIdealWeight_le_one (R : 𝓞 GaussianField) ι P.asIdeal)
  have hEuler := gaussian_smoothed_tsum_le_log_norm_of_euler_identity
    (quarticIdealWeight (R : 𝓞 GaussianField) ι)
    (norm_quarticIdealWeight_le_one (R : 𝓞 GaussianField) ι)
    B hB
    (LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ))
    hEulerIdentity
  exact quarticIdealZeroPrimeSum_le_loglog S
    (fun P => (quarticIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re)
    (64 * R.natAbs) (R : 𝓞 GaussianField) ι B σ
    reciprocalSquareConstant hB hσ₁ hσ₂ hperiod hmean hLpos
    hbelow habove hc hEuler

theorem anySignedIdealPrimeSum_le_coefficient_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (D : ℕ) (hD : 0 < D)
    (R : ℤ) (hR0 : R ≠ 0) (hR : R.natAbs ≤ D ^ 3)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (B : ℝ) (hB : 2 ≤ B) (hlogB : 1 ≤ Real.log B)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ)) :
    (∑ P ∈ S,
      (quarticIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re /
        (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * (D : ℝ))) +
        (Real.log 13 + Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + reciprocalSquareConstant) := by
  have hq : (1 : ℝ) ≤ (64 * R.natAbs : ℕ) := by
    have hn : 0 < R.natAbs := by omega
    exact_mod_cast (by omega : 1 ≤ 64 * R.natAbs)
  have hQ : 1 ≤ (((64 * R.natAbs : ℕ) : ℝ) ^ 2) := by nlinarith
  have hloglog := loglog_modulus_le_coefficient_loglog
    (D : ℝ) (((64 * R.natAbs : ℕ) : ℝ) ^ 2)
    (by exact_mod_cast hD) hQ
    (signedOddGaussianModulus_poly_bound D R hD hR)
  have hprime := anySignedIdealPrimeSum_le_loglog
    S R hR0 ι a ha hunit B hB hlogB hbelow habove
  linarith

end Erdos940.Quartic.GaussianAnyIdealPrimeSum
