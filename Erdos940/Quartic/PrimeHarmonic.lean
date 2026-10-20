import Erdos940.Quartic.EulerPrimeChebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A uniform prime harmonic sum

The elementary Chebyshev bound `θ(x) ≤ x log 4` and Abel summation give
`∑_{p≤B} 1/p ≤ (log 4) log log B + O(1)`.  The explicit coefficient
`log 4 < 10/7` is enough for the quartic local factor estimate.
-/

namespace Erdos940.Quartic

open Finset MeasureTheory intervalIntegral

noncomputable def rationalPrimeHarmonic (B : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE B, (p : ℝ)⁻¹

private noncomputable def primeHarmonicWeight (x : ℝ) : ℝ := (x * Real.log x)⁻¹

private theorem primeHarmonicWeight_deriv {x : ℝ} (hx : 1 < x) :
    deriv primeHarmonicWeight x =
      -(x ^ 2 * Real.log x)⁻¹ - (x ^ 2 * (Real.log x) ^ 2)⁻¹ := by
  have hx0 : x ≠ 0 := by linarith
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hd : HasDerivAt primeHarmonicWeight
      (-(x * Real.log x)⁻¹ ^ 2 * (Real.log x + 1)) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv
      (mul_ne_zero hx0 hl0) using 1
    · funext y
      rfl
    · simp only [Pi.mul_apply, id_eq, one_mul]
      field_simp
  rw [hd.deriv]
  field_simp; ring

private theorem primeHarmonicWeight_integrable (B : ℝ) :
    IntegrableOn (deriv primeHarmonicWeight) (Set.Icc 2 B) := by
  have hcont : ContinuousOn
      (fun x : ℝ => -(x ^ 2 * Real.log x)⁻¹ -
        (x ^ 2 * (Real.log x) ^ 2)⁻¹) (Set.Icc 2 B) := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1]
    have hx0 : x ≠ 0 := by linarith
    have hl0 : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
    have hfirst : ContinuousAt (fun y : ℝ => (y ^ 2 * Real.log y)⁻¹) x :=
      ((continuousAt_id.pow 2).mul hlog).inv₀
        (mul_ne_zero (pow_ne_zero _ hx0) hl0)
    have hsecond : ContinuousAt
        (fun y : ℝ => (y ^ 2 * (Real.log y) ^ 2)⁻¹) x :=
      ((continuousAt_id.pow 2).mul (hlog.pow 2)).inv₀
        (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hl0))
    exact (hfirst.neg.sub hsecond).continuousWithinAt
  apply ContinuousOn.integrableOn_Icc
  exact hcont.congr (by
    intro x hx
    exact primeHarmonicWeight_deriv (by linarith [hx.1]))

theorem rationalPrimeHarmonic_eq_theta_integral (B : ℝ) (hB : 2 ≤ B) :
    rationalPrimeHarmonic ⌊B⌋₊ =
      Chebyshev.theta B * primeHarmonicWeight B -
        ∫ t in 2..B, Chebyshev.theta t * deriv primeHarmonicWeight t := by
  classical
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n => Real.log n)
  have hsum : rationalPrimeHarmonic ⌊B⌋₊ =
      ∑ n ∈ Finset.Icc 0 ⌊B⌋₊, primeHarmonicWeight n * a n := by
    simp only [rationalPrimeHarmonic, Nat.primesLE_eq_filter_Icc_zero,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hln : Real.log (n : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      simp [a, hp, primeHarmonicWeight]
      field_simp
    · simp [a, hp]
  rw [hsum, sum_mul_eq_sub_integral_mul₁ a (f := primeHarmonicWeight)
    (by simp [a]) (by simp [a]) B (by
      intro x hx
      have hx1 : 1 < x := by linarith [hx.1]
      have hx0 : x ≠ 0 := by linarith
      have hl0 : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
      change DifferentiableAt ℝ (fun y : ℝ => (y * Real.log y)⁻¹) x
      exact ((differentiableAt_id.mul (Real.differentiableAt_log hx0)).inv
        (mul_ne_zero hx0 hl0))) (primeHarmonicWeight_integrable B)]
  have hsumTheta (x : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, a n) = Chebyshev.theta x := by
    simp [a, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      Set.indicator_apply]
  rw [hsumTheta B]
  rw [← intervalIntegral.integral_of_le hB]
  rw [show (fun t : ℝ => deriv primeHarmonicWeight t *
      ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) =
      (fun t : ℝ => Chebyshev.theta t * deriv primeHarmonicWeight t) from by
      funext t
      rw [hsumTheta]
      ring]
  ring

/-- Chebyshev's estimate gives the prime reciprocal sum with coefficient `log 4`. -/
theorem rationalPrimeHarmonic_le_loglog (B : ℝ) (hB : 3 ≤ B) :
    rationalPrimeHarmonic ⌊B⌋₊ ≤
      Real.log 4 * Real.log (Real.log B) +
        Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2)) := by
  have hB2 : 2 ≤ B := by linarith
  have hB1 : 1 < B := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  let g : ℝ → ℝ := fun t => t⁻¹ / Real.log t + t⁻¹ / Real.log t ^ 2
  have hmajor : ∀ t ∈ Set.Icc 2 B,
      -(Chebyshev.theta t * deriv primeHarmonicWeight t) ≤
        Real.log 4 * g t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos ht1
    have htheta := Chebyshev.theta_le_log4_mul_x ht0.le
    have hfactor : 0 ≤
        (t ^ 2 * Real.log t)⁻¹ + (t ^ 2 * (Real.log t) ^ 2)⁻¹ := by
      positivity
    have h := mul_le_mul_of_nonneg_right htheta hfactor
    rw [primeHarmonicWeight_deriv ht1]
    dsimp [g]
    convert h using 1 <;> field_simp <;> ring
  have hfirst : Chebyshev.theta B * primeHarmonicWeight B ≤
      Real.log 4 * (Real.log B)⁻¹ := by
    have htheta := Chebyshev.theta_le_log4_mul_x hB0.le
    have hf : 0 ≤ primeHarmonicWeight B := by
      dsimp [primeHarmonicWeight]
      positivity
    have h := mul_le_mul_of_nonneg_right htheta hf
    convert h using 1 <;> dsimp [primeHarmonicWeight] <;>
      field_simp
  have hgint : IntervalIntegrable g volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc 2 B := by simpa [Set.uIcc_of_le hB2] using ht
    have ht1 : 1 < t := by linarith [ht'.1]
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
    have hone : ContinuousAt (fun y : ℝ => y⁻¹ / Real.log y) t :=
      continuousAt_id.inv₀ ht0 |>.div hlog hlt
    have htwo : ContinuousAt (fun y : ℝ => y⁻¹ / Real.log y ^ 2) t :=
      continuousAt_id.inv₀ ht0 |>.div (hlog.pow 2) (pow_ne_zero _ hlt)
    exact (hone.add htwo).continuousWithinAt
  have honeInt : IntervalIntegrable
      (fun t : ℝ => t⁻¹ / Real.log t) volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc 2 B := by simpa [Set.uIcc_of_le hB2] using ht
    have ht1 : 1 < t := by linarith [ht'.1]
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    exact ((continuousAt_id.inv₀ ht0).div
      (Real.continuousAt_log ht0) hlt).continuousWithinAt
  have htwoInt : IntervalIntegrable
      (fun t : ℝ => t⁻¹ / Real.log t ^ 2) volume 2 B := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc 2 B := by simpa [Set.uIcc_of_le hB2] using ht
    have ht1 : 1 < t := by linarith [ht'.1]
    have ht0 : t ≠ 0 := by linarith
    have hlt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    exact ((continuousAt_id.inv₀ ht0).div
      ((Real.continuousAt_log ht0).pow 2) (pow_ne_zero _ hlt)).continuousWithinAt
  have hInt :
      (∫ t in 2..B, -(Chebyshev.theta t * deriv primeHarmonicWeight t)) ≤
        ∫ t in 2..B, Real.log 4 * g t := by
    apply intervalIntegral.integral_mono_on hB2
    · apply IntervalIntegrable.neg
      apply intervalIntegrable_iff.mpr
      rw [Set.uIoc_of_le hB2, ← integrableOn_Icc_iff_integrableOn_Ioc]
      conv => arg 1; ext t; rw [Chebyshev.theta_eq_sum_Icc, mul_comm,
        Finset.sum_filter]
      exact integrableOn_mul_sum_Icc _ (by norm_num)
        (primeHarmonicWeight_integrable B)
    · exact hgint.const_mul _
    · intro t ht
      exact hmajor t ht
  have hg : (∫ t in 2..B, Real.log 4 * g t) =
      Real.log 4 * (Real.log (Real.log B) - Real.log (Real.log 2) +
        (Real.log 2)⁻¹ - (Real.log B)⁻¹) := by
    rw [intervalIntegral.integral_const_mul]
    dsimp [g]
    rw [intervalIntegral.integral_add]
    · rw [integral_inv_div_log (by norm_num) hB1,
        integral_inv_div_log_sq (by norm_num) hB1]
      ring
    · exact honeInt
    · exact htwoInt
  rw [rationalPrimeHarmonic_eq_theta_integral B hB2]
  have hInt' : -(∫ t in 2..B, Chebyshev.theta t *
      deriv primeHarmonicWeight t) ≤
      ∫ t in 2..B, Real.log 4 * g t := by
    simpa only [intervalIntegral.integral_neg] using hInt
  calc
    _ ≤ Real.log 4 * (Real.log B)⁻¹ +
        Real.log 4 * (Real.log (Real.log B) - Real.log (Real.log 2) +
          (Real.log 2)⁻¹ - (Real.log B)⁻¹) := by linarith [hfirst, hInt', hg]
    _ = _ := by ring

/-- The numerical coefficient `10/7 = 30/21` is convenient when each
prime contributes at most `21/p` to an Euler product logarithm. -/
theorem rationalPrimeHarmonic_le_ten_sevenths_loglog (B : ℕ) (hB : 3 ≤ B) :
    rationalPrimeHarmonic B ≤
      (10 / 7 : ℝ) * Real.log (Real.log (2 * (B : ℝ))) +
        Real.log 4 * ((Real.log 2)⁻¹ - Real.log (Real.log 2)) := by
  have hBreal : (3 : ℝ) ≤ B := by exact_mod_cast hB
  have hbase := rationalPrimeHarmonic_le_loglog (B : ℝ) hBreal
  rw [Nat.floor_natCast] at hbase
  have hlogB : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogB_lower : 1 ≤ Real.log (B : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hBreal
    linarith [Real.log_three_gt_d9]
  have hloglogB : 0 ≤ Real.log (Real.log (B : ℝ)) :=
    Real.log_nonneg hlogB_lower
  have hBdouble : (B : ℝ) ≤ 2 * (B : ℝ) := by linarith
  have hlogBig : Real.log (B : ℝ) ≤ Real.log (2 * (B : ℝ)) :=
    Real.log_le_log (by exact_mod_cast (show 0 < B by omega)) hBdouble
  have hloglogBig : Real.log (Real.log (B : ℝ)) ≤
      Real.log (Real.log (2 * (B : ℝ))) :=
    Real.log_le_log hlogB hlogBig
  have hloglogBig_nonneg : 0 ≤ Real.log (Real.log (2 * (B : ℝ))) :=
    hloglogB.trans hloglogBig
  have hcoeff : Real.log 4 ≤ (10 / 7 : ℝ) := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hcoeff' : Real.log 4 * Real.log (Real.log (B : ℝ)) ≤
      (10 / 7 : ℝ) * Real.log (Real.log (2 * (B : ℝ))) := by
    calc
      _ ≤ Real.log 4 * Real.log (Real.log (2 * (B : ℝ))) :=
        mul_le_mul_of_nonneg_left hloglogBig (Real.log_nonneg (by norm_num))
      _ ≤ (10 / 7 : ℝ) * Real.log (Real.log (2 * (B : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoeff hloglogBig_nonneg
  linarith

/-- The exponential form used to bound the universal quartic local product. -/
theorem exp_twenty_one_prime_harmonic_le_log_pow_thirty (B : ℕ) (hB : 3 ≤ B) :
    Real.exp (21 * rationalPrimeHarmonic B) ≤
      Real.exp (21 * (Real.log 4 *
        ((Real.log 2)⁻¹ - Real.log (Real.log 2)))) *
          (Real.log (2 * (B : ℝ))) ^ 30 := by
  have hsum := rationalPrimeHarmonic_le_ten_sevenths_loglog B hB
  have hlogbig : 0 < Real.log (2 * (B : ℝ)) := by
    apply Real.log_pos
    have hb : (3 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hmul : 21 * rationalPrimeHarmonic B ≤
      30 * Real.log (Real.log (2 * (B : ℝ))) +
        21 * (Real.log 4 *
          ((Real.log 2)⁻¹ - Real.log (Real.log 2))) := by
    linarith
  have hpow : Real.exp (30 * Real.log (Real.log (2 * (B : ℝ)))) =
      (Real.log (2 * (B : ℝ))) ^ 30 := by
    rw [show (30 : ℝ) * Real.log (Real.log (2 * (B : ℝ))) =
      (30 : ℕ) * Real.log (Real.log (2 * (B : ℝ))) by norm_num]
    rw [Real.exp_nat_mul, Real.exp_log hlogbig]
  calc
    Real.exp (21 * rationalPrimeHarmonic B) ≤
        Real.exp (30 * Real.log (Real.log (2 * (B : ℝ))) +
          21 * (Real.log 4 *
            ((Real.log 2)⁻¹ - Real.log (Real.log 2)))) :=
      Real.exp_le_exp.mpr hmul
    _ = _ := by rw [Real.exp_add, hpow]; ring

/-- The same estimate applies to any chosen set of primes, including the
odd primes used in the local Euler product. -/
theorem exp_twenty_one_prime_subset_le_log_pow_thirty
    (B : ℕ) (S : Finset ℕ) (hB : 3 ≤ B)
    (hS : S ⊆ Nat.primesLE B) :
    Real.exp (21 * ∑ p ∈ S, (p : ℝ)⁻¹) ≤
      Real.exp (21 * (Real.log 4 *
        ((Real.log 2)⁻¹ - Real.log (Real.log 2)))) *
          (Real.log (2 * (B : ℝ))) ^ 30 := by
  have hsum : (∑ p ∈ S, (p : ℝ)⁻¹) ≤ rationalPrimeHarmonic B := by
    change (∑ p ∈ S, (p : ℝ)⁻¹) ≤
      ∑ p ∈ Nat.primesLE B, (p : ℝ)⁻¹
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro p _ _
    positivity
  apply (Real.exp_le_exp.mpr ?_).trans
    (exp_twenty_one_prime_harmonic_le_log_pow_thirty B hB)
  linarith

end Erdos940.Quartic
