import Erdos940.Quartic.GaussianIdealEulerProduct
import Erdos940.Quartic.GaussianIdealEulerIdentity

/-!
# Uniform Gaussian ideal Euler-log comparison

The prime-power error and absolute convergence use only the norm bound on
the ideal weight.  This applies equally to the type-zero quartic ideal
character and the type-two CM twist.
-/

namespace Erdos940.Quartic.GaussianIdealEulerUniversal

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianIdealEulerProduct
open Erdos940.Quartic.GaussianIdealEulerIdentity

/-- The smoothed prime term attached to a complex ideal weight. -/
noncomputable def gaussianPrimeTerm
    (w : Ideal (𝓞 GaussianField) → ℂ) (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) : ℂ :=
  (eulerMassTerm
    (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
      (Ideal.absNorm Q.asIdeal : ℝ)) B P : ℂ) * w P.asIdeal

/-- The real-smoothed prime factor is the prime term of the generic ideal
Dirichlet series at the corresponding complex exponent. -/
theorem gaussianPrimeTerm_eq_weightedIdealTerm
    (w : Ideal (𝓞 GaussianField) → ℂ) (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    gaussianPrimeTerm w B P =
      weightedIdealTerm w ((1 + 1 / Real.log B : ℝ) : ℂ) P.asIdeal := by
  have hn : 0 ≤ (P.asIdeal.absNorm : ℝ) := by positivity
  rw [gaussianPrimeTerm, eulerMassTerm_eq_rpow B P,
    weightedIdealTerm, if_neg P.ne_bot,
    Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow hn]
  simp only [Complex.ofReal_natCast, one_div, div_eq_mul_inv]
  ac_rfl

theorem gaussianPrimeTerm_re (w : Ideal (𝓞 GaussianField) → ℂ)
    (B : ℝ) (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (gaussianPrimeTerm w B P).re =
      eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
          (Ideal.absNorm Q.asIdeal : ℝ))
        (fun Q => (w Q.asIdeal).re) B P := by
  simp only [gaussianPrimeTerm, eulerMassTerm, eulerSmoothedTerm,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem gaussianPrimeTerm_norm_le_mass
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    ‖gaussianPrimeTerm w B P‖ ≤
      eulerMassTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
          (Ideal.absNorm Q.asIdeal : ℝ)) B P := by
  have hm : 0 ≤ eulerMassTerm
      (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
        (Ideal.absNorm Q.asIdeal : ℝ)) B P := by
    unfold eulerMassTerm
    positivity
  rw [gaussianPrimeTerm, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hm]
  exact mul_le_of_le_one_right hm (hw P.asIdeal)

theorem gaussianPrimeTerm_norm_le_inv
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (B : ℝ) (hB : 1 < B)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    ‖gaussianPrimeTerm w B P‖ ≤
      1 / (Ideal.absNorm P.asIdeal : ℝ) := by
  have hn : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm P
  have hlogn : 0 ≤ Real.log (Ideal.absNorm P.asIdeal : ℝ) :=
    Real.log_nonneg hn.le
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hexp : Real.exp
      (-(Real.log (Ideal.absNorm P.asIdeal : ℝ) / Real.log B)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr
      (div_nonneg hlogn hlogB.le))
  calc
    ‖gaussianPrimeTerm w B P‖ ≤
        eulerMassTerm
          (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
            (Ideal.absNorm Q.asIdeal : ℝ)) B P :=
      gaussianPrimeTerm_norm_le_mass w hw B P
    _ ≤ 1 / (Ideal.absNorm P.asIdeal : ℝ) := by
      unfold eulerMassTerm
      simpa using mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) by positivity)

theorem gaussianPrimeTerm_ne_one
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (B : ℝ) (hB : 1 < B)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    gaussianPrimeTerm w B P ≠ 1 := by
  intro h
  have hn : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm P
  have hlt : ‖gaussianPrimeTerm w B P‖ < 1 :=
    (gaussianPrimeTerm_norm_le_inv w hw B hB P).trans_lt
      (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hn)
  simp [h] at hlt

theorem gaussianPrimeTerm_summable
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (B : ℝ) (hB : 2 ≤ B) :
    Summable (gaussianPrimeTerm w B) := by
  have hmass := gaussianPrimeIdealMass_summable B hB
  have hnorm : Summable (fun P => ‖gaussianPrimeTerm w B P‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (gaussianPrimeTerm_norm_le_mass w hw B) hmass
  exact hnorm.of_norm

theorem gaussianPrimeTerm_sq_summable
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (B : ℝ) (hB : 1 < B) :
    Summable (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
      ‖gaussianPrimeTerm w B P‖ ^ 2) := by
  have hpoint (P : HeightOneSpectrum (𝓞 GaussianField)) :
      ‖gaussianPrimeTerm w B P‖ ^ 2 ≤
        (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by
    calc
      _ ≤ (1 / (Ideal.absNorm P.asIdeal : ℝ)) ^ 2 := by
        gcongr
        exact gaussianPrimeTerm_norm_le_inv w hw B hB P
      _ = (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by ring
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
    gaussianPrimeIdealReciprocalSquare_summable

theorem gaussianPrimeTerm_sq_tsum_le
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (B : ℝ) (hB : 1 < B) :
    (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      ‖gaussianPrimeTerm w B P‖ ^ 2) ≤
      2 * reciprocalSquareConstant := by
  have hpoint (P : HeightOneSpectrum (𝓞 GaussianField)) :
      ‖gaussianPrimeTerm w B P‖ ^ 2 ≤
        (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by
    calc
      _ ≤ (1 / (Ideal.absNorm P.asIdeal : ℝ)) ^ 2 := by
        gcongr
        exact gaussianPrimeTerm_norm_le_inv w hw B hB P
      _ = (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by ring
  exact ((gaussianPrimeTerm_sq_summable w hw B hB).tsum_le_tsum
    hpoint gaussianPrimeIdealReciprocalSquare_summable).trans
      gaussianPrimeIdealReciprocalSquare_tsum_le

/-- A uniform first-power Euler comparison for any ideal weight of norm at
most one. The exact Euler identity is the sole remaining premise. -/
theorem gaussian_smoothed_tsum_le_log_norm_of_euler_identity
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (B : ℝ) (hB : 2 ≤ B) (L : ℂ)
    (hEuler : Complex.exp
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - gaussianPrimeTerm w B P)) = L) :
    (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
          (Ideal.absNorm Q.asIdeal : ℝ))
        (fun Q => (w Q.asIdeal).re) B P) ≤
      Real.log ‖L‖ + reciprocalSquareConstant := by
  have hB' : 1 < B := by linarith
  have h := re_tsum_le_log_norm_of_exp_euler_log
    (gaussianPrimeTerm w B) L
    (gaussianPrimeTerm_ne_one w hw B hB')
    (gaussianPrimeTerm_summable w hw B hB)
    (gaussianPrimeTerm_sq_summable w hw B hB') hEuler
  rw [show (∑' P, (gaussianPrimeTerm w B P).re) =
    ∑' P : HeightOneSpectrum (𝓞 GaussianField),
      eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
          (Ideal.absNorm Q.asIdeal : ℝ))
        (fun Q => (w Q.asIdeal).re) B P from by
      congr 1
      funext P
      exact gaussianPrimeTerm_re w B P] at h
  have hsquare := gaussianPrimeTerm_sq_tsum_le w hw B hB'
  linarith

end Erdos940.Quartic.GaussianIdealEulerUniversal
