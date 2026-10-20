import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Comparing finite prime sums with Euler logarithms

This is the elementary comparison in equation (9) of the quartic Euler
majorant. The index type may be rational primes or prime ideals. The Euler
logarithm approximation, Chebyshev bound below the cutoff, and weighted tail
bound are explicit hypotheses; no specific L-function is defined here.
-/

namespace Erdos940.Quartic

open Finset

/-- The smoothed first-power term at the exponent `1 + 1/log B`. For
positive norm it equals `c(P) / norm(P)^(1+1/log B)`. -/
noncomputable def eulerSmoothedTerm {ι : Type*} (norm : ι → ℝ)
    (c : ι → ℝ) (B : ℝ) (P : ι) : ℝ :=
  c P / norm P * Real.exp (-(Real.log (norm P) / Real.log B))

/-- The nonnegative absolute envelope for a unit-bounded smoothed term. -/
noncomputable def eulerMassTerm {ι : Type*} (norm : ι → ℝ)
    (B : ℝ) (P : ι) : ℝ :=
  1 / norm P * Real.exp (-(Real.log (norm P) / Real.log B))

theorem eulerSmoothedTerm_neg_mass_le {ι : Type*}
    (norm : ι → ℝ) (c : ι → ℝ) (B : ℝ) (P : ι)
    (hnorm : 0 < norm P) (hc : |c P| ≤ 1) :
    -eulerMassTerm norm B P ≤ eulerSmoothedTerm norm c B P := by
  have hcLower : -1 ≤ c P := (abs_le.mp hc).1
  have hweight : 0 ≤ 1 / norm P *
      Real.exp (-(Real.log (norm P) / Real.log B)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcLower hweight
  dsimp [eulerMassTerm, eulerSmoothedTerm]
  convert hmul using 1 <;> ring

theorem eulerSmoothedTerm_eq_power {ι : Type*} (norm : ι → ℝ)
    (c : ι → ℝ) (B : ℝ) (P : ι) (hnorm : 0 < norm P) :
    eulerSmoothedTerm norm c B P =
      c P / (norm P) ^ (1 + 1 / Real.log B) := by
  have hscale : Real.log (norm P) / Real.log B =
      Real.log (norm P) * (1 / Real.log B) := by ring
  rw [Real.rpow_add hnorm, Real.rpow_one,
    Real.rpow_def_of_pos hnorm, ← hscale]
  simp [eulerSmoothedTerm, Real.exp_neg, div_eq_mul_inv]
  ring

/-- The signed tail lower bound needed in the Euler comparison follows
from an ordinary nonnegative tail-mass bound. This is the form supplied by
a Chebyshev estimate for prime ideals. -/
theorem eulerTail_lower_of_mass {ι : Type*} (S : Finset ι)
    (norm : ι → ℝ) (c : ι → ℝ) (B C : ℝ)
    (hnorm : ∀ P : (Sᶜ : Set ι), 0 < norm P)
    (hc : ∀ P : (Sᶜ : Set ι), |c P| ≤ 1)
    (hseries : Summable (eulerSmoothedTerm norm c B))
    (hmass : Summable (fun P : (Sᶜ : Set ι) => eulerMassTerm norm B P))
    (hbound : (∑' P : (Sᶜ : Set ι), eulerMassTerm norm B P) ≤ C) :
    -C ≤ ∑' P : (Sᶜ : Set ι), eulerSmoothedTerm norm c B P := by
  have hterm (P : (Sᶜ : Set ι)) :
      -eulerMassTerm norm B P ≤ eulerSmoothedTerm norm c B P :=
    eulerSmoothedTerm_neg_mass_le norm c B P (hnorm P) (hc P)
  have hle := hmass.neg.tsum_le_tsum hterm (hseries.subtype _)
  rw [tsum_neg] at hle
  linarith

/-- Pointwise smoothing loses at most `(log norm)/ (norm * log B)` when
`|c(P)| ≤ 1`. This is valid for coefficients of either sign. -/
theorem primeTerm_le_smoothed_add_error {ι : Type*}
    (norm : ι → ℝ) (c : ι → ℝ) (B : ℝ) (P : ι)
    (hB : 1 < B) (hnorm : 1 ≤ norm P) (hc : |c P| ≤ 1) :
    c P / norm P ≤ eulerSmoothedTerm norm c B P +
      (Real.log (norm P) / norm P) / Real.log B := by
  have hnormPos : 0 < norm P := zero_lt_one.trans_le hnorm
  have hlogNorm : 0 ≤ Real.log (norm P) := Real.log_nonneg hnorm
  have hlogB : 0 < Real.log B := Real.log_pos hB
  let u := Real.log (norm P) / Real.log B
  have hu : 0 ≤ u := div_nonneg hlogNorm hlogB.le
  have hexp : Real.exp (-u) ≤ 1 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (neg_nonpos.mpr hu))
  have hdelta : 0 ≤ 1 - Real.exp (-u) := sub_nonneg.mpr hexp
  have hdeltaLe : 1 - Real.exp (-u) ≤ u := by
    have h := Real.add_one_le_exp (-u)
    linarith
  have hcLe : c P ≤ 1 := (abs_le.mp hc).2
  have hwLe : c P / norm P ≤ 1 / norm P :=
    div_le_div_of_nonneg_right hcLe hnormPos.le
  have hfirst :
      c P / norm P ≤ c P / norm P * Real.exp (-u) +
        (1 / norm P) * (1 - Real.exp (-u)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hwLe) hdelta]
  have hsecond :
      (1 / norm P) * (1 - Real.exp (-u)) ≤
        (1 / norm P) * u :=
    mul_le_mul_of_nonneg_left hdeltaLe (by positivity)
  calc
    c P / norm P ≤ c P / norm P * Real.exp (-u) +
        (1 / norm P) * (1 - Real.exp (-u)) := hfirst
    _ ≤ c P / norm P * Real.exp (-u) + (1 / norm P) * u := by
      linarith
    _ = eulerSmoothedTerm norm c B P +
          (Real.log (norm P) / norm P) / Real.log B := by
      unfold eulerSmoothedTerm u
      ring

/-- An abstract Euler-log comparison. `hEuler` is the first-power Euler
series approximation to `log L`, with higher prime powers absorbed into
`eulerError`. The two Chebyshev consequences are `hChebBelow` and
`hTail`: the latter bounds the signed smoothed sum beyond the cutoff.
Together they give an error independent of the finite cutoff. -/
theorem finite_prime_sum_le_logL {ι : Type*} (S : Finset ι)
    (norm : ι → ℝ) (c : ι → ℝ) (B L : ℝ)
    (chebError tailError eulerError : ℝ)
    (hB : 1 < B)
    (hnorm : ∀ P ∈ S, 1 ≤ norm P)
    (hc : ∀ P ∈ S, |c P| ≤ 1)
    (hChebBelow : (∑ P ∈ S, Real.log (norm P) / norm P) ≤
      chebError * Real.log B)
    (hseries : Summable (eulerSmoothedTerm norm c B))
    (hTail : -tailError ≤
      ∑' P : (Sᶜ : Set ι), eulerSmoothedTerm norm c B P)
    (hEuler : (∑' P : ι, eulerSmoothedTerm norm c B P) ≤
      Real.log L + eulerError) :
    (∑ P ∈ S, c P / norm P) ≤
      Real.log L + chebError + tailError + eulerError := by
  classical
  have hterm : ∀ P ∈ S, c P / norm P ≤
      eulerSmoothedTerm norm c B P +
        (Real.log (norm P) / norm P) / Real.log B := by
    intro P hP
    exact primeTerm_le_smoothed_add_error norm c B P hB (hnorm P hP) (hc P hP)
  have hsum := Finset.sum_le_sum hterm
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hsmoothed :
      (∑ P ∈ S, c P / norm P) ≤
        (∑ P ∈ S, eulerSmoothedTerm norm c B P) + chebError := by
    have hsumError :
        (∑ P ∈ S, (Real.log (norm P) / norm P) / Real.log B) ≤
          chebError := by
      rw [← Finset.sum_div]
      exact (div_le_iff₀ hlogB).2 (by
        simpa only [mul_comm] using hChebBelow)
    rw [Finset.sum_add_distrib] at hsum
    linarith
  have hsplit := hseries.sum_add_tsum_compl (s := S)
  have hbelow :
      (∑ P ∈ S, eulerSmoothedTerm norm c B P) ≤
        (∑' P : ι, eulerSmoothedTerm norm c B P) + tailError := by
    linarith
  linarith

/-- A uniform bound `L ≤ K log(2Q)` converts the abstract comparison into
the `log log Q + O(1)` prime-sum majorant used in the quartic argument. -/
theorem finite_prime_sum_le_loglog_modulus {ι : Type*} (S : Finset ι)
    (norm : ι → ℝ) (c : ι → ℝ) (B L K Q : ℝ)
    (chebError tailError eulerError : ℝ)
    (hB : 1 < B) (hL : 0 < L) (hK : 0 < K) (hQ : 1 ≤ Q)
    (hLbound : L ≤ K * Real.log (2 * Q))
    (hnorm : ∀ P ∈ S, 1 ≤ norm P)
    (hc : ∀ P ∈ S, |c P| ≤ 1)
    (hChebBelow : (∑ P ∈ S, Real.log (norm P) / norm P) ≤
      chebError * Real.log B)
    (hseries : Summable (eulerSmoothedTerm norm c B))
    (hTail : -tailError ≤
      ∑' P : (Sᶜ : Set ι), eulerSmoothedTerm norm c B P)
    (hEuler : (∑' P : ι, eulerSmoothedTerm norm c B P) ≤
      Real.log L + eulerError) :
    (∑ P ∈ S, c P / norm P) ≤
      Real.log (Real.log (2 * Q)) +
        (Real.log K + chebError + tailError + eulerError) := by
  have hQ2 : 1 < 2 * Q := by nlinarith
  have hlogQ : 0 < Real.log (2 * Q) := Real.log_pos hQ2
  have hlogL : Real.log L ≤ Real.log K + Real.log (Real.log (2 * Q)) := by
    calc
      Real.log L ≤ Real.log (K * Real.log (2 * Q)) :=
        Real.log_le_log hL hLbound
      _ = Real.log K + Real.log (Real.log (2 * Q)) :=
        Real.log_mul hK.ne' hlogQ.ne'
  have hfirst := finite_prime_sum_le_logL S norm c B L
    chebError tailError eulerError hB hnorm hc hChebBelow hseries hTail hEuler
  linarith

end Erdos940.Quartic
