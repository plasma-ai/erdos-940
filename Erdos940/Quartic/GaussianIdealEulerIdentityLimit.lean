import Erdos940.Quartic.GaussianFiniteEulerLimit
import Erdos940.Quartic.GaussianCMCharacter
import Erdos940.Quartic.GaussianIdealEulerUniversal

/-!
# The Gaussian ideal Euler identity

Finite prime products are reindexed by ideal exponent vectors, then an
adaptive geometric cutoff compares their limits with the ideal Dirichlet
series. No Euler-product identity is assumed.
-/

namespace Erdos940.Quartic.GaussianIdealEulerIdentityLimit

open scoped NumberField Topology
open Filter
open IsDedekindDomain
open Erdos940.Quartic.GaussianIdealEulerIdentity
open Erdos940.Quartic.GaussianIdealExponentVectors
open Erdos940.Quartic.GaussianFiniteEulerLimit
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianCMCharacter
open Erdos940.Quartic.GaussianIdealEulerUniversal

theorem tendsto_sum_idealBox
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (σ : ℝ) (hσ : 1 < σ)
    (N : ℕ → ℕ) (hNmono : Monotone N) (hNlarge : ∀ n, n ≤ N n) :
    Tendsto (fun n => ∑ I ∈ idealBox (primeBox n) (N n),
      weightedIdealTerm w (σ : ℂ) I)
      atTop (𝓝 (∑' I : Ideal (𝓞 GaussianField),
        weightedIdealTerm w (σ : ℂ) I)) := by
  classical
  let box : ℕ → Finset (Ideal (𝓞 GaussianField)) :=
    fun n => insert ⊥ (idealBox (primeBox n) (N n))
  have hmono : Monotone box := by
    intro m n hmn
    apply Finset.insert_subset_insert
    exact (idealBox_mono_primes (primeBox_mono hmn) (N m)).trans
      ((idealBox_mono_cutoff (primeBox n)) (hNmono hmn))
  have hexhaustive (I : Ideal (𝓞 GaussianField)) : ∃ n, I ∈ box n := by
    by_cases hI : I = ⊥
    · exact ⟨0, by simp [box, hI]⟩
    obtain ⟨n, M, hmem⟩ := exists_mem_primeBox_idealBox I hI
    refine ⟨max n M, ?_⟩
    apply Finset.mem_insert_of_mem
    apply (idealBox_mono_cutoff (primeBox (max n M)))
      ((le_max_right n M).trans (hNlarge (max n M)))
    exact idealBox_mono_primes (primeBox_mono (le_max_left n M)) M hmem
  have hlimit := tendsto_sum_exhaustive_boxes
    (weightedIdealTerm w (σ : ℂ))
    (summable_weightedIdealTerm w hw σ hσ) box hmono hexhaustive
  have hsum (n : ℕ) :
      (∑ I ∈ box n, weightedIdealTerm w (σ : ℂ) I) =
      ∑ I ∈ idealBox (primeBox n) (N n), weightedIdealTerm w (σ : ℂ) I := by
    rw [show box n = insert ⊥ (idealBox (primeBox n) (N n)) from rfl,
      Finset.sum_insert (bot_not_mem_idealBox _ _)]
    simp [weightedIdealTerm]
  simpa only [hsum] using hlimit

/-- The exponential of the Gaussian prime logarithm is the ideal-indexed
Dirichlet series for any unit-bounded completely multiplicative weight. -/
theorem exp_prime_log_eq_tsum_weightedIdealTerm
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (σ : ℝ) (hσ : 1 < σ) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)) =
      ∑' I : Ideal (𝓞 GaussianField), weightedIdealTerm w (σ : ℂ) I := by
  classical
  let f (n k : ℕ) : ℂ :=
    ∏ P ∈ primeBox n, ∑ e ∈ Finset.range (k + 1),
      weightedIdealTerm w (σ : ℂ) (P.asIdeal ^ e)
  let g (n : ℕ) : ℂ :=
    ∏ P ∈ primeBox n,
      (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹
  have hf (n : ℕ) : Tendsto (f n) atTop (𝓝 (g n)) := by
    exact (tendsto_add_atTop_iff_nat 1).2
      (weightedIdeal_finitePrime_truncatedProduct_tendsto
        w hw hwone hwmul σ hσ (primeBox n))
  obtain ⟨N, hNmono, hNlarge, hclose⟩ :=
    exists_monotone_diagonal_cutoffs f g hf
  have hg : Tendsto g atTop
      (𝓝 (Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)))) := by
    exact tendsto_prod_exhaustive_boxes
      (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹)
      _ (hasProd_local_factor w hw σ hσ)
      primeBox primeBox_mono exists_mem_primeBox
  have hdiag : Tendsto (fun n => f n (N n)) atTop
      (𝓝 (Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hgl := tendsto_iff_dist_tendsto_zero.mp hg
    have hbound : Tendsto (fun n =>
        dist (f n (N n)) (g n) +
          dist (g n) (Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
            -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal))))
        atTop (𝓝 0) := by
      simpa using hclose.add hgl
    apply squeeze_zero (fun n => dist_nonneg)
      (fun n => dist_triangle (f n (N n)) (g n) _)
      hbound
  have hseries : Tendsto (fun n => f n (N n)) atTop
      (𝓝 (∑' I : Ideal (𝓞 GaussianField),
        weightedIdealTerm w (σ : ℂ) I)) := by
    convert tendsto_sum_idealBox w hw σ hσ N hNmono hNlarge using 1
    funext n
    exact finite_prime_product_eq_sum_idealBox
      w (σ : ℂ) hwone hwmul (primeBox n) (N n)
  exact tendsto_nhds_unique hdiag hseries

theorem exp_prime_log_eq_weightedIdealLSeries
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (σ : ℝ) (hσ : 1 < σ) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)) =
      LSeries (weightedIdealCoeff w) (σ : ℂ) := by
  rw [weightedIdealLSeries_eq_tsum_of_one_lt w hw σ hσ]
  exact exp_prime_log_eq_tsum_weightedIdealTerm w hw hwone hwmul σ hσ

theorem quartic_exp_prime_log_eq_LSeries
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (σ : ℝ) (hσ : 1 < σ) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - weightedIdealTerm (quarticIdealWeight R ι)
        (σ : ℂ) P.asIdeal)) =
      LSeries (quarticIdealCoeff R ι) (σ : ℂ) := by
  have hcoeff : weightedIdealCoeff (quarticIdealWeight R ι) =
      quarticIdealCoeff R ι := by
    funext n
    exact weightedIdealCoeff_eq_quarticIdealCoeff R ι n
  rw [← hcoeff]
  exact exp_prime_log_eq_weightedIdealLSeries
      (quarticIdealWeight R ι) (norm_quarticIdealWeight_le_one R ι)
      (quarticIdealWeight_top R ι)
      (GaussianIdealLBound.quarticIdealCoeff_weight_mul R ι) σ hσ

theorem eta_exp_prime_log_eq_LSeries
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (σ : ℝ) (hσ : 1 < σ) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - weightedIdealTerm (gaussianEtaIdealWeight R ι)
        (σ : ℂ) P.asIdeal)) =
      LSeries (gaussianEtaIdealCoeff R ι) (σ : ℂ) := by
  have hcoeff : weightedIdealCoeff (gaussianEtaIdealWeight R ι) =
      gaussianEtaIdealCoeff R ι := by
    funext n
    rfl
  rw [← hcoeff]
  exact exp_prime_log_eq_weightedIdealLSeries
    (gaussianEtaIdealWeight R ι)
    (norm_gaussianEtaIdealWeight_le_one R ι)
    (gaussianEtaIdealWeight_top R ι)
    (gaussianEtaIdealWeight_mul R ι) σ hσ

/-- Exact Euler identity at the smoothed exponent used by the quartic
prime-sum comparison. -/
theorem quartic_prime_euler_identity
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (B : ℝ) (hB : 1 < B) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - gaussianPrimeTerm (quarticIdealWeight R ι) B P)) =
      LSeries (quarticIdealCoeff R ι)
        ((1 + 1 / Real.log B : ℝ) : ℂ) := by
  have hσ : (1 : ℝ) < 1 + 1 / Real.log B := by
    have hlog : 0 < Real.log B := Real.log_pos hB
    have : 0 < 1 / Real.log B := by positivity
    linarith
  simpa only [gaussianPrimeTerm_eq_weightedIdealTerm] using
    quartic_exp_prime_log_eq_LSeries R ι _ hσ

/-- The same identity for the infinity-type-two CM twist. -/
theorem eta_prime_euler_identity
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (B : ℝ) (hB : 1 < B) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - gaussianPrimeTerm (gaussianEtaIdealWeight R ι) B P)) =
      LSeries (gaussianEtaIdealCoeff R ι)
        ((1 + 1 / Real.log B : ℝ) : ℂ) := by
  have hσ : (1 : ℝ) < 1 + 1 / Real.log B := by
    have hlog : 0 < Real.log B := Real.log_pos hB
    have : 0 < 1 / Real.log B := by positivity
    linarith
  simpa only [gaussianPrimeTerm_eq_weightedIdealTerm] using
    eta_exp_prime_log_eq_LSeries R ι _ hσ

end Erdos940.Quartic.GaussianIdealEulerIdentityLimit
