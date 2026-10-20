import Erdos940.Quartic.GaussianIdealEulerUniversal
import Erdos940.Quartic.GaussianIdealEulerIdentityLimit
import Erdos940.Quartic.GaussianCMCharacter
import Erdos940.Quartic.UniformEulerMajorant

/-!
# Uniform finite-prime bound for the Gaussian CM twist

The ideal Euler product, character bounds, and cutoff estimates are concrete.
-/

namespace Erdos940.Quartic.GaussianEtaPrimeSum

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianCMCharacter
open Erdos940.Quartic.GaussianIdealEulerUniversal
open Erdos940.Quartic.GaussianIdealEulerIdentityLimit

/-- The type-two CM constituent satisfies a prime-sum bound uniform in the radicand. The hypotheses
`hbelow` and `habove` assert that `S` is precisely the chosen norm cutoff. -/
theorem etaFinitePrimeSum_le_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (R : ℤ) (hR0 : R ≠ 0) (ι : GaussianField →+* ℂ)
    (B : ℝ) (hB : 2 ≤ B) (hlogB : 1 ≤ Real.log B)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ)) :
    (∑ P ∈ S,
      (gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re /
        (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * ((64 * R.natAbs : ℕ) : ℝ) ^ 2)) +
        (Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + reciprocalSquareConstant) := by
  let σ : ℝ := 1 + 1 / Real.log B
  let Q : ℝ := ((64 * R.natAbs : ℕ) : ℝ) ^ 2
  let K : ℝ := 162 + 648 / Real.log 2
  let L : ℝ := ‖LSeries (gaussianEtaIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖
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
          (gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι) B P)) =
      LSeries (gaussianEtaIdealCoeff (R : 𝓞 GaussianField) ι)
        (σ : ℂ) := by
    simpa only [σ, gaussianPrimeTerm_eq_weightedIdealTerm] using
      eta_exp_prime_log_eq_LSeries
        (R : 𝓞 GaussianField) ι σ hσ₁
  have hq : (1 : ℝ) ≤ (64 * R.natAbs : ℕ) := by
    have hn : 0 < R.natAbs := by omega
    exact_mod_cast (by omega : 1 ≤ 64 * R.natAbs)
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQle : Real.log Q ≤ Real.log (2 * Q) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have hlog2le : Real.log 2 ≤ Real.log (2 * Q) := by
    apply Real.log_le_log (by norm_num)
    nlinarith
  have h648 : 648 ≤ (648 / Real.log 2) * Real.log (2 * Q) := by
    have hscale : (648 / Real.log 2) * Real.log 2 = 648 := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hlog2le
      (show 0 ≤ 648 / Real.log 2 by positivity)
    linarith
  have hLbound : L ≤ K * Real.log (2 * Q) := by
    have h := norm_gaussianEtaIdealLSeries_le_log_signed
      R hR0 ι σ hσ₁ hσ₂
    have hnum : 0 ≤ 162 * Real.log Q + 648 := by positivity
    dsimp [L, K, Q] at *
    nlinarith
  have hLpos : 0 < L := by
    dsimp [L, σ]
    rw [← hEulerIdentity]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hc (P : HeightOneSpectrum (𝓞 GaussianField)) :
      |(gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans
      (norm_gaussianEtaIdealWeight_le_one (R : 𝓞 GaussianField) ι P.asIdeal)
  have hEuler := gaussian_smoothed_tsum_le_log_norm_of_euler_identity
    (gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι)
    (norm_gaussianEtaIdealWeight_le_one (R : 𝓞 GaussianField) ι)
    B hB
    (LSeries (gaussianEtaIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ))
    hEulerIdentity
  exact gaussianPrimeIdealFiniteSum_le_loglog S
    (fun P => (gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re)
    B L K Q reciprocalSquareConstant hB hLpos hK hQ hLbound
    hbelow habove hc hEuler

/-- With a cubic radicand bound, the η prime sum has the required
coefficient-uniform `log log(2D)` shape. -/
theorem etaFinitePrimeSum_le_coefficient_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (D : ℕ) (hD : 0 < D)
    (R : ℤ) (hR0 : R ≠ 0) (hR : R.natAbs ≤ D ^ 3)
    (ι : GaussianField →+* ℂ)
    (B : ℝ) (hB : 2 ≤ B) (hlogB : 1 ≤ Real.log B)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ)) :
    (∑ P ∈ S,
      (gaussianEtaIdealWeight (R : 𝓞 GaussianField) ι P.asIdeal).re /
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
  have hprime := etaFinitePrimeSum_le_loglog
    S R hR0 ι B hB hlogB hbelow habove
  linarith

end Erdos940.Quartic.GaussianEtaPrimeSum
