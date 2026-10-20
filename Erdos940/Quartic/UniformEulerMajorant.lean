import Erdos940.Quartic.ProgressionBuilder
import Erdos940.Quartic.EulerLogComparison
import Erdos940.Quartic.EulerPrimeChebyshev
import Erdos940.Quartic.GaussianHeckeLBridge
import Erdos940.Quartic.GaussianIdealLatticeSeries
import Erdos940.Quartic.GaussianIdealLBound
import Erdos940.Quartic.GaussianCharacters
import Erdos940.Quartic.GaussianPrimeIdealFibers
import Erdos940.Quartic.GaussianIdealEulerProduct

/-!
# Uniform Euler bound for the regular quartic base density

The eleven nonprincipal constituents are indexed by `Fin 11`. Their finite
prime sums are bounded through the L-function comparison separately, then
recombined into the local quartic trace. The character identification and
finite-modulus arithmetic appear as explicit hypotheses in the relevant
estimates.
-/

namespace Erdos940.Quartic

open Finset
open NumberField IsDedekindDomain
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianZeroMean

/-- A polynomial modulus bound transfers a character prime-sum estimate to
the coefficient-uniform logarithm. The exponent 13 accommodates moduli of
the form `(64R)²` with `R` bounded by a fixed cubic power of the coefficient
product. -/
theorem loglog_modulus_le_coefficient_loglog
    (D Q : ℝ) (hD : 1 ≤ D) (hQ : 1 ≤ Q)
    (hpoly : 2 * Q ≤ (2 * D) ^ (13 : ℕ)) :
    Real.log (Real.log (2 * Q)) ≤
      Real.log (Real.log (2 * D)) + Real.log 13 := by
  have h2D : 1 < 2 * D := by nlinarith
  have h2Q : 1 < 2 * Q := by nlinarith
  have hlogD : 0 < Real.log (2 * D) := Real.log_pos h2D
  have hlogQ : 0 < Real.log (2 * Q) := Real.log_pos h2Q
  have hlogbound : Real.log (2 * Q) ≤ 13 * Real.log (2 * D) := by
    have h := Real.log_le_log (by linarith : 0 < 2 * Q) hpoly
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    Real.log (Real.log (2 * Q)) ≤
        Real.log (13 * Real.log (2 * D)) :=
      Real.log_le_log hlogQ hlogbound
    _ = Real.log (Real.log (2 * D)) + Real.log 13 := by
      rw [Real.log_mul (by norm_num : (13 : ℝ) ≠ 0) hlogD.ne']
      ring

/-- The Gaussian candidate period `64|R|` has polynomial size when its
radicand is bounded by the cube of the coefficient product. -/
theorem signedOddGaussianModulus_poly_bound
    (D : ℕ) (R : ℤ) (hD : 0 < D) (hR : R.natAbs ≤ D ^ 3) :
    2 * (((64 * R.natAbs : ℕ) : ℝ) ^ 2) ≤
      (2 * (D : ℝ)) ^ (13 : ℕ) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hRreal : (R.natAbs : ℝ) ≤ (D : ℝ) ^ 3 := by exact_mod_cast hR
  have hDpow : (D : ℝ) ^ 6 ≤ (D : ℝ) ^ 13 := by
    exact pow_le_pow_right₀ hDreal (by decide)
  calc
    2 * (((64 * R.natAbs : ℕ) : ℝ) ^ 2) =
        8192 * (R.natAbs : ℝ) ^ 2 := by push_cast; ring
    _ ≤ 8192 * ((D : ℝ) ^ 3) ^ 2 := by gcongr
    _ = 8192 * (D : ℝ) ^ 6 := by ring
    _ ≤ 8192 * (D : ℝ) ^ 13 := by gcongr
    _ = (2 * (D : ℝ)) ^ (13 : ℕ) := by ring

/-- The uniform Gaussian prime-ideal estimate after the concrete splitting
count and Chebyshev bounds are inserted into the Euler-log comparison. The
Euler logarithm, character bound, and summability of its smoothed prime
series remain the L-function inputs. -/
theorem gaussianPrimeIdealFiniteSum_le_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ)
    (B L K Q eulerError : ℝ)
    (hB : 2 ≤ B) (hL : 0 < L) (hK : 0 < K) (hQ : 1 ≤ Q)
    (hLbound : L ≤ K * Real.log (2 * Q))
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ))
    (hc : ∀ P, |c P| ≤ 1)
    (hEuler :
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        eulerSmoothedTerm
          (fun P => (Ideal.absNorm P.asIdeal : ℝ)) c B P) ≤
        Real.log L + eulerError) :
    (∑ P ∈ S, c P / (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * Q)) +
        (Real.log K +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + eulerError) := by
  let N : HeightOneSpectrum (𝓞 GaussianField) → ℝ :=
    fun P => (Ideal.absNorm P.asIdeal : ℝ)
  let C : ℝ := 6 * Real.log 4 * (1 + 1 / Real.log 2)
  let T : ℝ := 2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
    reciprocalSquareConstant
  have hcheb : (∑ P ∈ S, Real.log (N P) / N P) ≤
      C * Real.log B :=
    gaussianPrimeIdealLogSum_le S B hB hbelow
  have htailBound :
      (∑' P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
        eulerMassTerm N B P.val) ≤ T :=
    gaussianPrimeIdealTailMass_le S B hB habove
  have hmass : Summable
      (fun P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))) =>
        eulerMassTerm N B P.val) :=
    gaussianPrimeIdealTailMass_summable S B hB habove
  have hseries : Summable (eulerSmoothedTerm N c B) := by
    apply (Finset.summable_compl_iff (s := S)).1
    apply hmass.of_norm_bounded
    intro P
    have hN : 0 < N P.val := lt_trans (by linarith : 0 < B) (habove P)
    have hc' : |c P.val| ≤ 1 := hc P.val
    change ‖c P.val / N P.val *
      Real.exp (-(Real.log (N P.val) / Real.log B))‖ ≤
      1 / N P.val * Real.exp (-(Real.log (N P.val) / Real.log B))
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos hN, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc' hN.le) (Real.exp_pos _).le
  have htail : -T ≤
      ∑' P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
        eulerSmoothedTerm N c B P.val :=
    eulerTail_lower_of_mass S N c B T
      (fun P => lt_trans (by linarith : 0 < B) (habove P))
      (fun P => hc P) hseries hmass htailBound
  have hnorm (P : HeightOneSpectrum (𝓞 GaussianField)) (hP : P ∈ S) :
      1 ≤ N P := by
    have hn : 0 < Ideal.absNorm P.asIdeal := by
      rw [← gaussianPrime_absNorm_pow_inertiaDeg P]
      exact pow_pos (gaussianBasePrime P).property.pos _
    dsimp [N]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  exact finite_prime_sum_le_loglog_modulus S N c B L K Q C T eulerError
    (by linarith) hL hK hQ hLbound hnorm (fun P _ => hc P)
    hcheb hseries htail hEuler

/-- The type-zero Gaussian quartic ideal character has the required finite
prime-sum bound once its Euler-log comparison is known. The fixed constant
comes from the lattice estimate and does not depend on the quartic radicand
or on the prime cutoff. -/
theorem quarticIdealZeroPrimeSum_le_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ)
    (q : ℕ) [NeZero q] (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ)
    (B σ eulerError : ℝ)
    (hB : 2 ≤ B) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι))
    (hmean : (∑ uv : Fin q × Fin q,
      residueWeight q (quarticIdealLatticeWeight R ι) uv) = 0)
    (hLpos : 0 < ‖LSeries (quarticIdealCoeff R ι) (σ : ℂ)‖)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ))
    (hc : ∀ P, |c P| ≤ 1)
    (hEuler :
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        eulerSmoothedTerm
          (fun P => (Ideal.absNorm P.asIdeal : ℝ)) c B P) ≤
        Real.log ‖LSeries (quarticIdealCoeff R ι) (σ : ℂ)‖ + eulerError) :
    (∑ P ∈ S, c P / (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * (q : ℝ) ^ 2)) +
        (Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + eulerError) := by
  let Q : ℝ := (q : ℝ) ^ 2
  let K : ℝ := 162 + 648 / Real.log 2
  let L : ℝ := ‖LSeries (quarticIdealCoeff R ι) (σ : ℂ)‖
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have h2Q : 0 < 2 * Q := by positivity
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlogQle : Real.log Q ≤ Real.log (2 * Q) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  have hlog2le : Real.log 2 ≤ Real.log (2 * Q) := by
    apply Real.log_le_log (by norm_num)
    nlinarith
  have h648 : 648 ≤ (648 / Real.log 2) * Real.log (2 * Q) := by
    have hscale : (648 / Real.log 2) * Real.log 2 = 648 := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_left hlog2le
      (show 0 ≤ 648 / Real.log 2 by positivity)
    linarith
  have hLbound : L ≤ K * Real.log (2 * Q) := by
    have h := norm_quarticIdealLSeries_le_log q R ι
      hperiod hmean σ hσ₁ hσ₂
    have hnum : 0 ≤ 162 * Real.log Q + 648 := by positivity
    dsimp [L, K, Q] at *
    nlinarith
  exact gaussianPrimeIdealFiniteSum_le_loglog S c B L K Q eulerError
    hB hLpos hK hQ hLbound hbelow habove hc hEuler

/-- For a nonzero odd rational radicand, a nontrivial residue-unit multiplier
supplies both periodicity and zero mean. The sole remaining analytic input
is the first-power Euler-log comparison for this ideal character. -/
theorem quarticSignedOddIdealPrimeSum_le_loglog
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ)
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (B σ eulerError : ℝ)
    (hB : 2 ≤ B) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hLpos : 0 <
      ‖LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ))
    (hc : ∀ P, |c P| ≤ 1)
    (hEuler :
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        eulerSmoothedTerm
          (fun P => (Ideal.absNorm P.asIdeal : ℝ)) c B P) ≤
        Real.log
          ‖LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖ +
          eulerError) :
    (∑ P ∈ S, c P / (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * ((64 * R.natAbs : ℕ) : ℝ) ^ 2)) +
        (Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + eulerError) := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  exact quarticIdealZeroPrimeSum_le_loglog S c (64 * R.natAbs)
    (R : 𝓞 GaussianField) ι B σ eulerError hB hσ₁ hσ₂
    (quarticIdealLatticeWeight_signed_odd_periodic R hR0 hRodd ι)
    (quarticIdealLatticeWeight_signed_residue_mean_zero_of_multiplier
      R hR0 hRodd ι a ha hunit)
    hLpos hbelow habove hc hEuler

/-- The signed-odd type-zero Gaussian constituent needs only its exact
prime-ideal Euler product identity. Its L-series bound, nonvanishing,
smoothed prime summability, square error, and prime tail are all supplied
by the preceding results. -/
theorem quarticSignedOddIdealPrimeSum_le_loglog_of_euler_identity
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (B : ℝ) (hB : 2 ≤ B) (hlogB : 1 ≤ Real.log B)
    (hbelow : ∀ P ∈ S, (Ideal.absNorm P.asIdeal : ℝ) ≤ B)
    (habove : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ))
    (hEulerIdentity : Complex.exp
      (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - GaussianIdealEulerProduct.quarticPrimeTerm
          (R : 𝓞 GaussianField) ι B P)) =
      LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι)
        ((1 + 1 / Real.log B : ℝ) : ℂ)) :
    (∑ P ∈ S,
      (GaussianIdealLatticeSeries.quarticIdealWeight
        (R : 𝓞 GaussianField) ι P.asIdeal).re /
        (Ideal.absNorm P.asIdeal : ℝ)) ≤
      Real.log (Real.log (2 * ((64 * R.natAbs : ℕ) : ℝ) ^ 2)) +
        (Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) + reciprocalSquareConstant) := by
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
  have hLpos : 0 <
      ‖LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖ := by
    rw [← hEulerIdentity]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hc (P : HeightOneSpectrum (𝓞 GaussianField)) :
      |(GaussianIdealLatticeSeries.quarticIdealWeight
        (R : 𝓞 GaussianField) ι P.asIdeal).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans
      (norm_quarticIdealWeight_le_one (R : 𝓞 GaussianField) ι P.asIdeal)
  have hEuler :=
    GaussianIdealEulerProduct.quartic_smoothed_tsum_le_log_norm_of_euler_identity
      (R : 𝓞 GaussianField) ι B hB
      (LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ))
      hEulerIdentity
  exact quarticSignedOddIdealPrimeSum_le_loglog S
    (fun P => (GaussianIdealLatticeSeries.quarticIdealWeight
      (R : 𝓞 GaussianField) ι P.asIdeal).re)
    R hR0 hRodd ι a ha hunit B σ reciprocalSquareConstant
    hB hσ₁ hσ₂ hLpos hbelow habove hc hEuler

/-- Summing eleven constituent bounds gives the trace bound in (10). The
`error` also includes the bounded inert-prime contribution. -/
theorem quarticTrace_sum_le_eleven_loglog
    (S : Finset ℕ) (A : ℕ → ℝ) (c : Fin 11 → ℕ → ℝ)
    (D error : ℝ) (_hD : 1 ≤ D)
    (htrace : ∀ p ∈ S, A p = ∑ j : Fin 11, c j p)
    (hconstituent : ∀ j : Fin 11,
      (∑ p ∈ S, c j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * D)) + error) :
    (∑ p ∈ S, A p / (p : ℝ)) ≤
      11 * Real.log (Real.log (2 * D)) + 11 * error := by
  have hsum : (∑ p ∈ S, A p / (p : ℝ)) =
      ∑ j : Fin 11, ∑ p ∈ S, c j p / (p : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [htrace p hp, Finset.sum_div]
  rw [hsum]
  calc
    _ ≤ ∑ _j : Fin 11, (Real.log (Real.log (2 * D)) + error) :=
      Finset.sum_le_sum (fun j _ => hconstituent j)
    _ = 11 * Real.log (Real.log (2 * D)) + 11 * error := by
      simp

/-- The eleven prime-sum estimates and the summable reciprocal-square error
give a cutoff-independent Euler-product bound. A local factor may vanish. -/
theorem quarticEulerProduct_le_log_pow_eleven
    (S : Finset ℕ) (A : ℕ → ℝ) (c : Fin 11 → ℕ → ℝ)
    (D error : ℝ) (hD : 1 ≤ D)
    (hpos : ∀ p ∈ S, 0 < p)
    (hA : ∀ p ∈ S, |A p| ≤ 21)
    (hfactor : ∀ p ∈ S, 0 ≤ quarticEulerFactor p (A p))
    (htrace : ∀ p ∈ S, A p = ∑ j : Fin 11, c j p)
    (hconstituent : ∀ j : Fin 11,
      (∑ p ∈ S, c j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * D)) + error) :
    (∏ p ∈ S, quarticEulerFactor p (A p)) ≤
      Real.exp (11 * error + 21 * reciprocalSquareConstant) *
        Real.log (2 * D) ^ (11 : ℕ) := by
  have hD2 : 1 < 2 * D := by nlinarith
  have hlogD : 0 < Real.log (2 * D) := Real.log_pos hD2
  have hsum := quarticTrace_sum_le_eleven_loglog S A c D error hD
    htrace hconstituent
  have hprod := quarticEulerProduct_le_exp_uniform S A hpos hA hfactor
  have hexp :
      Real.exp ((∑ p ∈ S, A p / (p : ℝ)) +
        21 * reciprocalSquareConstant) ≤
      Real.exp (11 * Real.log (Real.log (2 * D)) +
        11 * error + 21 * reciprocalSquareConstant) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow : Real.exp (11 * Real.log (Real.log (2 * D))) =
      Real.log (2 * D) ^ (11 : ℕ) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hlogD] using
      (Real.exp_nat_mul (Real.log (Real.log (2 * D))) 11)
  calc
    (∏ p ∈ S, quarticEulerFactor p (A p)) ≤
        Real.exp ((∑ p ∈ S, A p / (p : ℝ)) +
          21 * reciprocalSquareConstant) := hprod
    _ ≤ Real.exp (11 * Real.log (Real.log (2 * D)) +
          11 * error + 21 * reciprocalSquareConstant) := hexp
    _ = Real.exp (11 * error + 21 * reciprocalSquareConstant) *
          Real.log (2 * D) ^ (11 : ℕ) := by
      rw [show 11 * Real.log (Real.log (2 * D)) +
          11 * error + 21 * reciprocalSquareConstant =
          11 * Real.log (Real.log (2 * D)) +
            (11 * error + 21 * reciprocalSquareConstant) by ring,
        Real.exp_add, hpow]
      ring

/-- Separate coefficient primes from good primes. The former cost at most
four each; the eleven character estimates control the latter uniformly in
the prime cutoff. -/
theorem quarticProduct_le_bad_four_mul_log_pow_eleven
    (S : Finset ℕ) (f A : ℕ → ℝ) (bad : ℕ → Prop)
    [DecidablePred bad] (c : Fin 11 → ℕ → ℝ)
    (D error : ℝ) (hD : 1 ≤ D)
    (hpos : ∀ p ∈ S, 0 < p)
    (hnonneg : ∀ p ∈ S, 0 ≤ f p)
    (hbad : ∀ p ∈ S, bad p → f p ≤ 4)
    (hgood : ∀ p ∈ S, ¬bad p → f p ≤ quarticEulerFactor p (A p))
    (hA : ∀ p ∈ S.filter (fun p => ¬bad p), |A p| ≤ 21)
    (htrace : ∀ p ∈ S.filter (fun p => ¬bad p),
      A p = ∑ j : Fin 11, c j p)
    (hconstituent : ∀ j : Fin 11,
      (∑ p ∈ S.filter (fun p => ¬bad p), c j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * D)) + error) :
    (∏ p ∈ S, f p) ≤
      (4 : ℝ) ^ (S.filter bad).card *
        (Real.exp (11 * error + 21 * reciprocalSquareConstant) *
          Real.log (2 * D) ^ (11 : ℕ)) := by
  let G := S.filter (fun p => ¬bad p)
  let H := S.filter bad
  have hfact (p : ℕ) (hp : p ∈ G) :
      0 ≤ quarticEulerFactor p (A p) :=
    (hnonneg p (Finset.mem_filter.mp hp).1).trans
      (hgood p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
  have hEuler := quarticEulerProduct_le_log_pow_eleven G A c D error hD
    (fun p hp => hpos p (Finset.mem_filter.mp hp).1)
    hA hfact htrace hconstituent
  have hbadprod : (∏ p ∈ H, f p) ≤ (4 : ℝ) ^ H.card := by
    calc
      (∏ p ∈ H, f p) ≤ ∏ _p ∈ H, (4 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact hnonneg p (Finset.mem_filter.mp hp).1
        · intro p hp
          exact hbad p (Finset.mem_filter.mp hp).1
            (Finset.mem_filter.mp hp).2
      _ = (4 : ℝ) ^ H.card := by simp
  have hgoodprod : (∏ p ∈ G, f p) ≤
      ∏ p ∈ G, quarticEulerFactor p (A p) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      exact hnonneg p (Finset.mem_filter.mp hp).1
    · intro p hp
      exact hgood p (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2
  have hsplit : (∏ p ∈ S, f p) =
      (∏ p ∈ H, f p) * (∏ p ∈ G, f p) := by
    simpa only [H, G] using (Finset.prod_filter_mul_prod_filter_not S bad f).symm
  rw [hsplit]
  exact (mul_le_mul hbadprod hgoodprod
    (Finset.prod_nonneg fun p hp =>
      hnonneg p (Finset.mem_filter.mp hp).1)
    (by positivity)).trans
    (mul_le_mul_of_nonneg_left hEuler (by positivity))

/-- The base density is exactly the dyadic factor times the odd-prime
valuation-one factors. This remains true when the progression also contains
selected primes, since its base target is fixed modulo every base modulus. -/
theorem quarticBaseDensity_eq_dyadic_mul_primeProduct
    (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts) :
    quarticBaseDensity B Q hQ d =
      localDensityFactor 16 (fun i => (d i).val) 8 *
        ∏ p ∈ quarticBasePrimes B,
          localDensityFactor (p ^ 2) (fun i => (d i).val) p := by
  classical
  let S := quarticBasePrimes B
  let d₀ : Fin 4 → ℕ := fun i => (d i).val
  let a := quarticProgressionResidue B Q hQ
  have hnot : 16 ∉ S.image (fun p => p ^ 2) := by
    intro hmem
    obtain ⟨p, hp, hp16⟩ := Finset.mem_image.mp hmem
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp4 : p = 4 := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (by simpa only [show 16 = 4 ^ 2 by decide] using hp16)
    have : ¬Nat.Prime 4 := by decide
    exact this (hp4 ▸ hpprime)
  have hinj : Function.Injective (fun p : ℕ => p ^ 2) :=
    Nat.pow_left_injective (by decide)
  unfold quarticBaseDensity quarticBaseModuli
  change (∏ m ∈ insert 16 (S.image (fun p => p ^ 2)),
    localDensityFactor m d₀ a) = _
  rw [Finset.prod_insert hnot, Finset.prod_image hinj.injOn]
  have h16 : localDensityFactor 16 d₀ a =
      localDensityFactor 16 d₀ 8 :=
    localDensityFactor_congr_target 16 (by decide) d₀ a 8
      (quarticProgressionResidue_mod_sixteen B Q hQ)
  rw [h16]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpS : p ∈ quarticSievePrimes B Q :=
    Finset.mem_union_left Q hp
  exact localDensityFactor_congr_target (p ^ 2)
    (pow_ne_zero _ hpprime.ne_zero) d₀ a p
    (quarticProgressionResidue_mod_prime_square B Q hQ p hpS)

/-- A good base-prime factor costs at most `exp(21/p)`. This is the pointwise
input for the unrestricted part of the quartic progression estimate. -/
theorem quarticBaseGoodFactor_le_exp
    (B p : ℕ) (hp : p ∈ quarticBasePrimes B)
    (d : Fin 4 → CanonicalParts) (A : ℝ)
    (hgood : ∀ i, ¬p ∣ (d i).val)
    (hA : |A| ≤ 21)
    (hlocal :
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
        (p : ℝ) ^ 3 =
          1 + A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹)) :
    localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
      Real.exp (21 / (p : ℝ)) := by
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hgt : 2 < p := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    omega
  letI : Fact p.Prime := ⟨hprime⟩
  have hfour : (4 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hzero
    have htwo : p ∣ 2 :=
      hprime.dvd_of_dvd_pow (by simpa only [show 4 = 2 ^ 2 by decide] using hdiv)
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp htwo
    omega
  have hunit (i : Fin 4) : ((d i).val : ZMod p) ≠ 0 := by
    intro hi
    exact hgood i ((ZMod.natCast_eq_zero_iff (d i).val p).mp hi)
  have htr :
      (localQuarticCount (ZMod p) 0
        (fun i => ((d i).val : ZMod p)) : ℝ) / (p : ℝ) ^ 3 =
          1 + A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
    simpa only [localQuarticCount, Nat.card_eq_fintype_card] using hlocal
  have heq := localDensityFactor_good_prime_formula p hprime
    (fun i => (d i).val) A hunit hfour htr
  have hAle : A ≤ 21 := (abs_le.mp hA).2
  calc
    localDensityFactor (p ^ 2) (fun i => (d i).val) p =
        quarticSelectedFactor p A := by
      simpa only [quarticSelectedFactor] using heq
    _ ≤ 1 + 21 / (p : ℝ) :=
      quarticSelectedFactor_le_one_add_twentyone_div p hprime.pos A hAle
    _ ≤ Real.exp (21 / (p : ℝ)) := by
      simpa only [add_comm] using Real.add_one_le_exp (21 / (p : ℝ))

/-- Equation (15) for the actual base density. The eleven finite prime-sum
estimates and their identification with the quartic trace are the precise
arithmetic inputs. The local congruence factors, coefficient-prime cost, and
Euler-product algebra are all discharged here. -/
theorem quarticBaseDensity_le_uniformEuler
    (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts)
    (A : ℕ → ℝ) (c : Fin 11 → ℕ → ℝ) (error : ℝ)
    (hA : ∀ p ∈ (quarticBasePrimes B).filter
      (fun p => ∀ i, ¬p ∣ (d i).val), |A p| ≤ 21)
    (hlocal : ∀ p ∈ (quarticBasePrimes B).filter
      (fun p => ∀ i, ¬p ∣ (d i).val),
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
        (p : ℝ) ^ 3 =
          1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hcharacter : ∀ p ∈ (quarticBasePrimes B).filter
      (fun p => ∀ i, ¬p ∣ (d i).val),
      A p = ∑ j : Fin 11, c j p)
    (hconstituent : ∀ j : Fin 11,
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val), c j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + error) :
    quarticBaseDensity B Q hQ d ≤
      (16 * Real.exp (11 * error + 21 * reciprocalSquareConstant)) *
        (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ) := by
  classical
  let S := quarticBasePrimes B
  let f : ℕ → ℝ := fun p =>
    localDensityFactor (p ^ 2) (fun i => (d i).val) p
  let bad : ℕ → Prop := fun p => ∃ i, p ∣ (d i).val
  have hDpos : 0 < coefficientProduct d := by
    unfold coefficientProduct
    exact Finset.prod_pos (fun i _ => CanonicalPart.pos (d i).property)
  have hD : (1 : ℝ) ≤ (coefficientProduct d : ℝ) := by
    exact_mod_cast hDpos
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (Finset.mem_filter.mp hp).2
  have hodd (p : ℕ) (hp : p ∈ S) : 2 < p := by
    have hge := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    omega
  have hfour (p : ℕ) (hp : p ∈ S) : (4 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hzero
    have htwo : p ∣ 2 :=
      (hprime p hp).dvd_of_dvd_pow (by simpa only [show 4 = 2 ^ 2 by decide] using hdiv)
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (hprime p hp) Nat.prime_two).mp htwo
    have hgt := hodd p hp
    omega
  have hbad (p : ℕ) (hp : p ∈ S) (hb : bad p) : f p ≤ 4 := by
    letI : Fact p.Prime := ⟨hprime p hp⟩
    exact localDensityFactor_prime_square_le_four p (hprime p hp)
      (fun i => (d i).val)
      (fun i hdiv => canonicalPart_prime_square_dvd (d i) p
        (hprime p hp) hdiv)
      (hfour p hp)
  have hgood (p : ℕ) (hp : p ∈ S) (hb : ¬bad p) :
      f p ≤ quarticEulerFactor p (A p) := by
    letI : Fact p.Prime := ⟨hprime p hp⟩
    have hunit (i : Fin 4) : ((d i).val : ZMod p) ≠ 0 := by
      intro hi
      exact hb ⟨i, (ZMod.natCast_eq_zero_iff (d i).val p).mp hi⟩
    have hnone (i : Fin 4) : ¬p ∣ (d i).val := by
      intro hi
      exact hb ⟨i, hi⟩
    have hpGood : p ∈ S.filter (fun p => ∀ i, ¬p ∣ (d i).val) :=
      Finset.mem_filter.mpr ⟨hp, hnone⟩
    have htr :
        (localQuarticCount (ZMod p) 0
          (fun i => ((d i).val : ZMod p)) : ℝ) / (p : ℝ) ^ 3 =
          1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
      simpa only [localQuarticCount, Nat.card_eq_fintype_card] using
        hlocal p hpGood
    have heq := localDensityFactor_good_prime_formula p (hprime p hp)
      (fun i => (d i).val) (A p) hunit (hfour p hp) htr
    have hle := quarticSelectedFactor_le_quarticEulerFactor p
      (hprime p hp).pos (A p)
    simpa only [f, quarticSelectedFactor] using heq.le.trans hle
  have hnonneg (p : ℕ) (hp : p ∈ S) : 0 ≤ f p :=
    localDensityFactor_nonneg (p ^ 2) _ _
  have hprod := quarticProduct_le_bad_four_mul_log_pow_eleven
    S f A bad c (coefficientProduct d : ℝ) error hD
    (fun p hp => (hprime p hp).pos) hnonneg hbad hgood
    (by simpa only [S, bad, not_exists] using hA)
    (by simpa only [S, bad, not_exists] using hcharacter)
    (by simpa only [S, bad, not_exists] using hconstituent)
  have hcard : (S.filter bad).card ≤
      (coefficientProduct d).primeFactors.card := by
    simpa only [S, bad] using
      quartic_coefficient_prime_filter_card_le S d hprime
  have hpow : (4 : ℝ) ^ (S.filter bad).card ≤
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card :=
    pow_le_pow_right₀ (by norm_num) hcard
  have hlogD : 0 ≤ Real.log (2 * (coefficientProduct d : ℝ)) := by
    apply Real.log_nonneg
    nlinarith
  have hprod' : (∏ p ∈ S, f p) ≤
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        (Real.exp (11 * error + 21 * reciprocalSquareConstant) *
          Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)) :=
    hprod.trans (mul_le_mul_of_nonneg_right hpow (by positivity))
  have hdyadic := localDensityFactor_sixteen_le_sixteen
    (fun i => (d i).val) 8
  have hprodNonneg : 0 ≤ ∏ p ∈ S, f p :=
    Finset.prod_nonneg hnonneg
  rw [quarticBaseDensity_eq_dyadic_mul_primeProduct B Q hQ d]
  change localDensityFactor 16 (fun i => (d i).val) 8 *
      (∏ p ∈ S, f p) ≤ _
  calc
    _ ≤ 16 * ((4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          (Real.exp (11 * error + 21 * reciprocalSquareConstant) *
            Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ))) :=
      mul_le_mul hdyadic hprod' hprodNonneg (by norm_num)
    _ = (16 * Real.exp (11 * error + 21 * reciprocalSquareConstant)) *
          (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
            Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ) := by ring

end Erdos940.Quartic
