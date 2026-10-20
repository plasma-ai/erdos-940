import Erdos940.Quartic.GaussianIdealLBound
import Erdos940.Quartic.GaussianPrimeIdealFibers
import Erdos940.Quartic.EulerLogComparison
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# The Gaussian ideal Euler logarithm

The elementary logarithmic inequality here gives the prime-power error
without needing a branch choice for a complex logarithm. An Euler-product
identity will connect it to the norm-indexed ideal L-series.
-/

namespace Erdos940.Quartic.GaussianIdealEulerProduct

open scoped NumberField
open Finset
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries

private theorem goodIdeal_top (R : 𝓞 GaussianField) :
    GaussianQuarticGoodIdeal R ⊤ := by
  refine ⟨by simp, ?_⟩
  intro P hP
  have hunit : IsUnit P.asIdeal := isUnit_of_dvd_one (by simpa using hP)
  exact (P.isPrime.ne_top (Ideal.isUnit_iff.mp hunit)).elim

/-- The extended quartic ideal character is normalized at the unit ideal. -/
theorem quarticIdealWeight_top (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) : quarticIdealWeight R ι ⊤ = 1 := by
  have hgood := goodIdeal_top R
  have hnorm : ‖quarticIdealWeight R ι ⊤‖ = 1 := by
    simp only [quarticIdealWeight, dif_pos hgood]
    exact norm_gaussianQuarticComplexValue ι _
  have hmul := GaussianIdealLBound.quarticIdealCoeff_weight_mul R ι ⊤ ⊤
  have hmul' : quarticIdealWeight R ι ⊤ =
      quarticIdealWeight R ι ⊤ * quarticIdealWeight R ι ⊤ := by
    simpa using hmul
  have hnonzero : quarticIdealWeight R ι ⊤ ≠ 0 := by
    intro hz
    simp [hz] at hnorm
  have hcancel : quarticIdealWeight R ι ⊤ * 1 =
      quarticIdealWeight R ι ⊤ * quarticIdealWeight R ι ⊤ := by
    simpa using hmul'
  exact (mul_left_cancel₀ hnonzero hcancel).symm

/-- The first Euler coefficient is below the real logarithm of the inverse
Euler factor up to half the squared coefficient norm. -/
theorem re_le_neg_log_norm_one_sub_add_half_sq (z : ℂ) (hz : z ≠ 1) :
    z.re ≤ -Real.log ‖(1 : ℂ) - z‖ + ‖z‖ ^ 2 / 2 := by
  have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hnorm : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr hne
  have hlog := Real.log_le_sub_one_of_pos (sq_pos_of_pos hnorm)
  have hlog_sq : Real.log (‖(1 : ℂ) - z‖ ^ 2) =
      2 * Real.log ‖(1 : ℂ) - z‖ := by
    rw [pow_two, Real.log_mul (ne_of_gt hnorm) (ne_of_gt hnorm)]
    ring
  have hnormsq : ‖(1 : ℂ) - z‖ ^ 2 =
      1 - 2 * z.re + ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  rw [hlog_sq, hnormsq] at hlog
  linarith

/-- The analytic part of the Euler comparison, separated from unique
factorization of ideals.  The hypothesis is the exact logarithmic Euler
identity, while the error is just the sum of squared prime coefficients. -/
theorem re_tsum_le_log_norm_of_exp_euler_log
    {α : Type*} (z : α → ℂ) (L : ℂ)
    (hz : ∀ a, z a ≠ 1) (hsum : Summable z)
    (hsq : Summable fun a => ‖z a‖ ^ 2)
    (hEuler : Complex.exp (∑' a, -Complex.log (1 - z a)) = L) :
    (∑' a, (z a).re) ≤ Real.log ‖L‖ + (∑' a, ‖z a‖ ^ 2) / 2 := by
  have hlog : Summable (fun a => -Complex.log (1 - z a)) :=
    hsum.clog_one_sub.neg
  have hlogRe : Summable (fun a => -Real.log ‖1 - z a‖) := by
    have hlogRe' : Summable (fun a => (-Complex.log (1 - z a)).re) :=
      ⟨_, Complex.hasSum_re hlog.choose_spec⟩
    convert hlogRe' using 1
    ext a
    simp [Complex.log_re]
  have hsumRe : Summable (fun a => (z a).re) :=
    ⟨_, Complex.hasSum_re hsum.choose_spec⟩
  have hbound : Summable (fun a => -Real.log ‖1 - z a‖ + ‖z a‖ ^ 2 / 2) :=
    hlogRe.add (hsq.div_const 2)
  have hpoint (a : α) :
      (z a).re ≤ -Real.log ‖1 - z a‖ + ‖z a‖ ^ 2 / 2 :=
    re_le_neg_log_norm_one_sub_add_half_sq (z a) (hz a)
  have htsum := hsumRe.tsum_le_tsum hpoint hbound
  have hreal :
      (∑' a, -Real.log ‖1 - z a‖) = Real.log ‖L‖ := by
    calc
      _ = (∑' a, -Complex.log (1 - z a)).re := by
        rw [Complex.re_tsum hlog]
        congr 1
        funext a
        simp [Complex.log_re]
      _ = Real.log ‖L‖ := by rw [← hEuler, Complex.norm_exp, Real.log_exp]
  rw [hlogRe.tsum_add (hsq.div_const 2), tsum_div_const, hreal] at htsum
  exact htsum

/-- The first prime-ideal term for the quartic ideal weight, at the
exponent selected by the Euler majorant cutoff `B`. -/
noncomputable def quarticPrimeTerm (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) : ℂ :=
  (eulerMassTerm (fun Q : HeightOneSpectrum (𝓞 GaussianField) =>
    (Q.asIdeal.absNorm : ℝ)) B P : ℂ) * quarticIdealWeight R ι P.asIdeal

/-- The real part of the complex Euler term is the signed smoothed term
used by the finite-prime majorant. -/
theorem quarticPrimeTerm_re (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (quarticPrimeTerm R ι B P).re =
      eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) => (Q.asIdeal.absNorm : ℝ))
        (fun Q => (quarticIdealWeight R ι Q.asIdeal).re) B P := by
  simp only [quarticPrimeTerm, eulerMassTerm, eulerSmoothedTerm,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The real smoothing factor is the reciprocal norm power at the
selected exponent. -/
theorem eulerMassTerm_eq_rpow (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    eulerMassTerm
      (fun Q : HeightOneSpectrum (𝓞 GaussianField) => (Q.asIdeal.absNorm : ℝ))
      B P =
      1 / (P.asIdeal.absNorm : ℝ) ^ (1 + 1 / Real.log B) := by
  have hn : 0 < (P.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm P))
  calc
    _ = eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) => (Q.asIdeal.absNorm : ℝ))
        (fun _ => 1) B P := by
      simp [eulerMassTerm, eulerSmoothedTerm]
    _ = _ := eulerSmoothedTerm_eq_power _ _ B P hn

/-- The quartic prime Euler factor written as a norm-power denominator. -/
theorem quarticPrimeTerm_eq_weight_div_cpow
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (B : ℝ) (P : HeightOneSpectrum (𝓞 GaussianField)) :
    quarticPrimeTerm R ι B P =
      quarticIdealWeight R ι P.asIdeal /
        (P.asIdeal.absNorm : ℂ) ^ ((1 + 1 / Real.log B : ℝ) : ℂ) := by
  have hn : 0 ≤ (P.asIdeal.absNorm : ℝ) := by positivity
  rw [quarticPrimeTerm, eulerMassTerm_eq_rpow B P]
  rw [Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_cpow hn]
  simp only [Complex.ofReal_natCast, one_div, div_eq_mul_inv]
  ac_rfl

/-- Uniform domination of a smoothed quartic prime factor by the reciprocal
of its ideal norm. -/
theorem quarticPrimeTerm_norm_le_inv (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ) (hB : 1 < B)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    ‖quarticPrimeTerm R ι B P‖ ≤
      1 / (Ideal.absNorm P.asIdeal : ℝ) := by
  let n : ℝ := (Ideal.absNorm P.asIdeal : ℝ)
  have hn : 1 < n := by
    dsimp [n]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm P
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn.le
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hexp : Real.exp (-(Real.log n / Real.log B)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (div_nonneg hlogn hlogB.le))
  have hm : 0 ≤ 1 / n * Real.exp (-(Real.log n / Real.log B)) := by positivity
  have hw := norm_quarticIdealWeight_le_one R ι P.asIdeal
  calc
    ‖quarticPrimeTerm R ι B P‖ =
        (1 / n * Real.exp (-(Real.log n / Real.log B))) *
          ‖quarticIdealWeight R ι P.asIdeal‖ := by
      rw [quarticPrimeTerm, norm_mul]
      dsimp only [eulerMassTerm]
      rw [Complex.norm_real, Real.norm_eq_abs]
      change |1 / n * Real.exp (-(Real.log n / Real.log B))| *
        ‖quarticIdealWeight R ι P.asIdeal‖ = _
      rw [abs_of_nonneg hm]
    _ ≤ 1 / n * Real.exp (-(Real.log n / Real.log B)) := by
      exact mul_le_of_le_one_right hm hw
    _ ≤ 1 / n := by
      have hnonneg : 0 ≤ 1 / n := by positivity
      nlinarith
    _ = 1 / (Ideal.absNorm P.asIdeal : ℝ) := rfl

/-- Every smoothed quartic prime factor has norm strictly below one. -/
theorem quarticPrimeTerm_norm_lt_one (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ) (hB : 1 < B)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    ‖quarticPrimeTerm R ι B P‖ < 1 := by
  have hn : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm P
  exact (quarticPrimeTerm_norm_le_inv R ι B hB P).trans_lt
    (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hn)

theorem quarticPrimeTerm_ne_one (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ) (hB : 1 < B)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    quarticPrimeTerm R ι B P ≠ 1 := by
  intro h
  have hlt := quarticPrimeTerm_norm_lt_one R ι B hB P
  simp [h] at hlt

/-- The absolute norm of a Gaussian prime ideal is at least the rational
prime below it. -/
private theorem gaussianBasePrime_le_absNorm
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (gaussianBasePrime P).val ≤ Ideal.absNorm P.asIdeal := by
  rw [← gaussianPrime_absNorm_pow_inertiaDeg]
  exact le_self_pow (Nat.one_le_of_lt (gaussianBasePrime P).property.one_lt)
    (Nat.ne_of_gt (Ideal.inertiaDeg_pos P.asIdeal ℤ))

/-- The finite Gaussian prime-ideal reciprocal-square sums are bounded by
twice the rational reciprocal-square constant. -/
theorem gaussianPrimeIdealReciprocalSquare_finset_le
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField))) :
    (∑ P ∈ F, (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2) ≤
      2 * reciprocalSquareConstant := by
  classical
  have hterm (P : HeightOneSpectrum (𝓞 GaussianField)) :
      (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 ≤
        1 / ((gaussianBasePrime P).val : ℝ) ^ 2 := by
    have hbase : (0 : ℝ) < (gaussianBasePrime P).val := by
      exact_mod_cast (gaussianBasePrime P).property.pos
    have hle : ((gaussianBasePrime P).val : ℝ) ≤
        (Ideal.absNorm P.asIdeal : ℝ) := by
      exact_mod_cast gaussianBasePrime_le_absNorm P
    apply one_div_le_one_div_of_le (sq_pos_of_pos hbase)
    gcongr
  calc
    (∑ P ∈ F, (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2) ≤
        ∑ P ∈ F, 1 / ((gaussianBasePrime P).val : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro P _
      exact hterm P
    _ ≤ 2 * ∑ p ∈ F.image gaussianBasePrime,
        (1 : ℝ) / (p.val : ℝ) ^ 2 :=
      sum_over_prime_fibers_le F gaussianBasePrime
        (fun p => (1 : ℝ) / (p.val : ℝ) ^ 2) 2
        (fun _ => by positivity) (gaussianBasePrime_fiber_card_le_two F)
    _ ≤ 2 * reciprocalSquareConstant := by
      gcongr
      have hinj : Function.Injective (fun p : Nat.Primes => p.val) :=
        Subtype.val_injective
      rw [← Finset.sum_image (s := F.image gaussianBasePrime)
        (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
        (fun p _ q _ h => hinj h)]
      exact finite_reciprocalSquares_le _

/-- The entire Gaussian prime-ideal reciprocal-square series converges. -/
theorem gaussianPrimeIdealReciprocalSquare_summable :
    Summable (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
      (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2) := by
  refine summable_of_sum_le (c := 2 * reciprocalSquareConstant)
    (fun _ => by positivity) ?_
  intro F
  exact gaussianPrimeIdealReciprocalSquare_finset_le F

theorem gaussianPrimeIdealReciprocalSquare_tsum_le :
    (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2) ≤
      2 * reciprocalSquareConstant := by
  apply Real.tsum_le_of_sum_le (fun _ => by positivity)
  intro F
  exact gaussianPrimeIdealReciprocalSquare_finset_le F

/-- The higher-power error for the quartic Euler logarithm is uniformly
bounded; it is independent of the cutoff and of the quartic conductor. -/
theorem quarticPrimeTerm_sq_summable (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ) (hB : 1 < B) :
    Summable (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
      ‖quarticPrimeTerm R ι B P‖ ^ 2) := by
  have hpoint (P : HeightOneSpectrum (𝓞 GaussianField)) :
      ‖quarticPrimeTerm R ι B P‖ ^ 2 ≤
        (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by
    calc
      _ ≤ (1 / (Ideal.absNorm P.asIdeal : ℝ)) ^ 2 := by
        gcongr
        exact quarticPrimeTerm_norm_le_inv R ι B hB P
      _ = (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by ring
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
    gaussianPrimeIdealReciprocalSquare_summable

theorem quarticPrimeTerm_sq_tsum_le (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ) (hB : 1 < B) :
    (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      ‖quarticPrimeTerm R ι B P‖ ^ 2) ≤
      2 * reciprocalSquareConstant := by
  have hpoint (P : HeightOneSpectrum (𝓞 GaussianField)) :
      ‖quarticPrimeTerm R ι B P‖ ^ 2 ≤
        (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by
    calc
      _ ≤ (1 / (Ideal.absNorm P.asIdeal : ℝ)) ^ 2 := by
        gcongr
        exact quarticPrimeTerm_norm_le_inv R ι B hB P
      _ = (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) ^ 2 := by ring
  exact ((quarticPrimeTerm_sq_summable R ι B hB).tsum_le_tsum
    hpoint gaussianPrimeIdealReciprocalSquare_summable).trans
      gaussianPrimeIdealReciprocalSquare_tsum_le

/-- There are finitely many Gaussian prime ideals of bounded norm. -/
theorem finite_gaussianPrimes_absNorm_le (N : ℕ) :
    {P : HeightOneSpectrum (𝓞 GaussianField) |
      Ideal.absNorm P.asIdeal ≤ N}.Finite := by
  have hfin := (Ideal.finite_setOfPred_absNorm_le N :
    {I : Ideal (𝓞 GaussianField) | Ideal.absNorm I ≤ N}.Finite)
  change (HeightOneSpectrum.asIdeal ⁻¹'
    {I : Ideal (𝓞 GaussianField) | Ideal.absNorm I ≤ N}).Finite
  exact Set.Finite.preimage
    (fun _ _ _ _ h => HeightOneSpectrum.asIdeal_injective h) hfin

noncomputable def smallGaussianPrimes (B : ℝ) :
    Finset (HeightOneSpectrum (𝓞 GaussianField)) :=
  (finite_gaussianPrimes_absNorm_le ⌈B⌉₊).toFinset

theorem smallGaussianPrimes_compl_gt (B : ℝ)
    (P : ((smallGaussianPrimes B : Finset
      (HeightOneSpectrum (𝓞 GaussianField)))ᶜ : Set
        (HeightOneSpectrum (𝓞 GaussianField)))) :
    B < (Ideal.absNorm P.val.asIdeal : ℝ) := by
  have hnot : ¬ Ideal.absNorm P.val.asIdeal ≤ ⌈B⌉₊ := by
    have hnotmem : P.val ∉ smallGaussianPrimes B := by
      exact P.property
    intro h
    apply hnotmem
    simp [smallGaussianPrimes, h]
  have hgt : ⌈B⌉₊ < Ideal.absNorm P.val.asIdeal := Nat.lt_of_not_ge hnot
  exact lt_of_le_of_lt (Nat.le_ceil B) (by exact_mod_cast hgt)

/-- The Gaussian prime-ideal smoothing mass is summable for `B ≥ 2`. -/
theorem gaussianPrimeIdealMass_summable (B : ℝ) (hB : 2 ≤ B) :
    Summable (eulerMassTerm
      (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        (Ideal.absNorm P.asIdeal : ℝ)) B) := by
  classical
  let S := smallGaussianPrimes B
  let mass : HeightOneSpectrum (𝓞 GaussianField) → ℝ :=
    eulerMassTerm (fun P => (Ideal.absNorm P.asIdeal : ℝ)) B
  have htail : Summable (fun P : (Sᶜ : Set
      (HeightOneSpectrum (𝓞 GaussianField))) => mass P.val) :=
    gaussianPrimeIdealTailMass_summable S B hB
      (by intro P; exact smallGaussianPrimes_compl_gt B P)
  have htailI : Summable ((Sᶜ : Set
      (HeightOneSpectrum (𝓞 GaussianField))).indicator mass) :=
    summable_subtype_iff_indicator.mp htail
  have hfinite : Summable ((S : Set
      (HeightOneSpectrum (𝓞 GaussianField))).indicator mass) :=
    summable_subtype_iff_indicator.mp (S.finite_toSet.summable mass)
  change Summable mass
  apply (hfinite.add htailI).congr
  intro P
  by_cases hP : P ∈ S
  · simp [Set.indicator, hP]
  · simp [Set.indicator, hP]

/-- The smoothed prime-ideal Euler terms form an absolutely convergent
series for every cutoff `B ≥ 2`. -/
theorem quarticPrimeTerm_summable (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (B : ℝ) (hB : 2 ≤ B) :
    Summable (quarticPrimeTerm R ι B) := by
  let mass : HeightOneSpectrum (𝓞 GaussianField) → ℝ :=
    eulerMassTerm (fun P => (Ideal.absNorm P.asIdeal : ℝ)) B
  have hmass : Summable mass := gaussianPrimeIdealMass_summable B hB
  have hnorm (P : HeightOneSpectrum (𝓞 GaussianField)) :
      ‖quarticPrimeTerm R ι B P‖ ≤ mass P := by
    have hm : 0 ≤ mass P := by
      dsimp [mass, eulerMassTerm]
      positivity
    rw [quarticPrimeTerm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hm]
    exact mul_le_of_le_one_right hm
      (norm_quarticIdealWeight_le_one R ι P.asIdeal)
  have hnormSum : Summable (fun P => ‖quarticPrimeTerm R ι B P‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hmass
  exact hnormSum.of_norm

/-- Concrete first-power comparison. The remaining `hEuler` premise is
the prime-ideal Euler product for the norm-indexed quartic ideal series. -/
theorem quartic_smoothed_tsum_le_log_norm
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (B : ℝ)
    (L : ℂ) (C : ℝ)
    (hne : ∀ P, quarticPrimeTerm R ι B P ≠ 1)
    (hsum : Summable (quarticPrimeTerm R ι B))
    (hsq : Summable fun P => ‖quarticPrimeTerm R ι B P‖ ^ 2)
    (hsqBound : (∑' P, ‖quarticPrimeTerm R ι B P‖ ^ 2) ≤ C)
    (hEuler : Complex.exp
      (∑' P, -Complex.log (1 - quarticPrimeTerm R ι B P)) = L) :
    (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) => (Q.asIdeal.absNorm : ℝ))
        (fun Q => (quarticIdealWeight R ι Q.asIdeal).re) B P) ≤
      Real.log ‖L‖ + C / 2 := by
  have h := re_tsum_le_log_norm_of_exp_euler_log
    (quarticPrimeTerm R ι B) L hne hsum hsq hEuler
  simpa only [quarticPrimeTerm_re] using h.trans (by gcongr)

/-- The concrete Euler-log comparison at the quartic ideal character.
Only the exact ideal Euler-product identity remains as a premise. -/
theorem quartic_smoothed_tsum_le_log_norm_of_euler_identity
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (B : ℝ) (hB : 2 ≤ B) (L : ℂ)
    (hEuler : Complex.exp
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - quarticPrimeTerm R ι B P)) = L) :
    (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      eulerSmoothedTerm
        (fun Q : HeightOneSpectrum (𝓞 GaussianField) => (Q.asIdeal.absNorm : ℝ))
        (fun Q => (quarticIdealWeight R ι Q.asIdeal).re) B P) ≤
      Real.log ‖L‖ + reciprocalSquareConstant := by
  have hB' : 1 < B := by linarith
  have h := quartic_smoothed_tsum_le_log_norm R ι B L
    (2 * reciprocalSquareConstant)
    (quarticPrimeTerm_ne_one R ι B hB')
    (quarticPrimeTerm_summable R ι B hB)
    (quarticPrimeTerm_sq_summable R ι B hB')
    (quarticPrimeTerm_sq_tsum_le R ι B hB') hEuler
  convert h using 1 <;> ring

end Erdos940.Quartic.GaussianIdealEulerProduct
