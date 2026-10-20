import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The logarithmic initial segment of a Gaussian Hecke L-series

The usual bound for a Gaussian Hecke L-value separates the series at the
conductor norm `Q`. On the initial segment a linear bound on cumulative
absolute coefficients gives a harmonic sum, at most `1 + log Q`.
The tail additionally needs cancellation in the partial sums of coefficients.
-/

namespace Erdos940.Quartic.GaussianLBoundAnalytic

open Finset

/-- A cumulative linear bound on nonnegative coefficients controls their
harmonically weighted sum. -/
theorem sum_div_le_harmonic_of_partial_sum_le (a : ℕ → ℝ) (C : ℝ)
    (hA : ∀ n, (∑ i ∈ Icc 1 n, a i) ≤ C * n) (Q : ℕ) :
    (∑ n ∈ Icc 1 Q, a n / n) ≤ C * (harmonic Q : ℝ) := by
  let A (n : ℕ) : ℝ := ∑ i ∈ Icc 1 n, a i
  let W (n : ℕ) : ℝ := ∑ i ∈ Icc 1 n, a i / i
  have hmain : ∀ n : ℕ, 1 ≤ n →
      W n ≤ A n / n + C * ((harmonic n : ℝ) - 1) := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst n
        simp [W, A, harmonic_eq_sum_Icc]
      · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn'
        have hnp : (0 : ℝ) < n + 1 := by positivity
        have hAn : A n ≤ C * n := hA n
        have hstep : A n / n - A n / (n + 1 : ℝ) ≤ C / (n + 1 : ℝ) := by
          have hdiff : A n / n - A n / (n + 1 : ℝ) =
              A n / ((n : ℝ) * (n + 1)) := by field_simp; ring
          rw [hdiff]
          calc
            A n / ((n : ℝ) * (n + 1)) ≤
                (C * n) / ((n : ℝ) * (n + 1)) :=
              div_le_div_of_nonneg_right hAn (le_of_lt (mul_pos hnr hnp))
            _ = C / (n + 1 : ℝ) := by field_simp
        have hAsucc : A (n + 1) = A n + a (n + 1) := by
          simp [A, sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
        have hWsucc : W (n + 1) = W n + a (n + 1) / (n + 1 : ℝ) := by
          simp [W, sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
        rw [hWsucc, hAsucc, harmonic_succ]
        push_cast
        have hi := ih hn'
        calc
          W n + a (n + 1) / (↑n + 1) ≤
              A n / n + C * ((harmonic n : ℝ) - 1) + a (n + 1) / (↑n + 1) := by
            simpa only [add_comm] using
              (add_le_add_right hi (a (n + 1) / (↑n + 1)))
          _ = (A n / n - A n / (↑n + 1)) +
              ((A n + a (n + 1)) / (↑n + 1) +
                C * ((harmonic n : ℝ) - 1)) := by ring
          _ ≤ C / (↑n + 1) +
              ((A n + a (n + 1)) / (↑n + 1) +
                C * ((harmonic n : ℝ) - 1)) := by
            simpa only [add_comm] using
              (add_le_add_right hstep
                ((A n + a (n + 1)) / (↑n + 1) + C * ((harmonic n : ℝ) - 1)))
          _ = (A n + a (n + 1)) / (↑n + 1) +
                C * ((harmonic n : ℝ) + (↑n + 1)⁻¹ - 1) := by
            rw [div_eq_mul_inv]
            ring
  by_cases hQ : Q = 0
  · simp [hQ]
  · have hQ' : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ'
    have hAQ : A Q / Q ≤ C := by
      apply (div_le_iff₀ hQr).mpr
      exact hA Q
    have := hmain Q hQ'
    dsimp [W] at this
    nlinarith

/-- The initial segment of an L-series is bounded by a harmonic sum whenever
the cumulative norms of its coefficients are at most `C n`. This estimate is
uniform for real `σ ≥ 1`. -/
theorem norm_initial_segment_le_harmonic (f : ℕ → ℂ) (σ C : ℝ) (Q : ℕ)
    (hσ : 1 ≤ σ)
    (hf : ∀ n, (∑ i ∈ Icc 1 n, ‖f i‖) ≤ C * n) :
    ‖∑ n ∈ Icc 1 Q, LSeries.term f (σ : ℂ) n‖ ≤ C * (harmonic Q : ℝ) := by
  calc
    ‖∑ n ∈ Icc 1 Q, LSeries.term f (σ : ℂ) n‖
        ≤ ∑ n ∈ Icc 1 Q, ‖LSeries.term f (σ : ℂ) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 Q, ‖f n‖ / n := by
      apply sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1)
      have hterm := LSeries.norm_term_le_of_re_le_re f
        (s := (1 : ℂ)) (s' := (σ : ℂ)) (by simpa using hσ) n
      have hnorm : ‖LSeries.term f (1 : ℂ) n‖ = ‖f n‖ * (n : ℝ)⁻¹ := by
        rw [LSeries.norm_term_eq]
        simp [hn0, div_eq_mul_inv]
      calc
        ‖LSeries.term f (σ : ℂ) n‖ ≤ ‖LSeries.term f (1 : ℂ) n‖ := hterm
        _ = ‖f n‖ * (n : ℝ)⁻¹ := hnorm
        _ = ‖f n‖ / n := by rw [div_eq_mul_inv]
    _ ≤ C * (harmonic Q : ℝ) :=
      sum_div_le_harmonic_of_partial_sum_le (fun n => ‖f n‖) C hf Q

/-- The logarithmic bound for the initial segment, uniform as `σ` approaches
one from above. -/
theorem norm_initial_segment_le_log (f : ℕ → ℂ) (σ C : ℝ) (Q : ℕ)
    (hσ : 1 ≤ σ) (hC : 0 ≤ C)
    (hf : ∀ n, (∑ i ∈ Icc 1 n, ‖f i‖) ≤ C * n) :
    ‖∑ n ∈ Icc 1 Q, LSeries.term f (σ : ℂ) n‖ ≤ C * (1 + Real.log Q) := by
  exact (norm_initial_segment_le_harmonic f σ C Q hσ hf).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Q) hC)

/-- A linear bound on cumulative absolute coefficients supplies the growth
hypothesis used by Mathlib's Abel representation of an L-series. -/
theorem sum_norm_isBigO_natCast (f : ℕ → ℂ) (C : ℝ)
    (hAbs : ∀ n, (∑ k ∈ Icc 1 n, ‖f k‖) ≤ C * n) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖f k‖) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, Filter.Eventually.of_forall (fun n => ?_)⟩
  have hnonneg : 0 ≤ ∑ k ∈ Icc 1 n, ‖f k‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.rpow_one] using hAbs n

/-- A power majorant with exponent below `-1` gives an explicit bound on an
improper integral. In the Hecke application, the integrand is the partial
coefficient sum times the derivative of `t ^ (-σ)`. -/
theorem norm_integral_Ioi_le_rpow (g : ℝ → ℂ) (A a R : ℝ)
    (ha : a < -1) (hR : 0 < R)
    (hg : ∀ t, R < t → ‖g t‖ ≤ A * t ^ a) :
    ‖∫ t in Set.Ioi R, g t‖ ≤ A * (-R ^ (a + 1) / (a + 1)) := by
  have hInt : MeasureTheory.IntegrableOn (fun t : ℝ => A * t ^ a) (Set.Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt ha hR).const_mul A
  have hle : ‖∫ t in Set.Ioi R, g t‖ ≤ ∫ t in Set.Ioi R, A * t ^ a :=
    MeasureTheory.norm_integral_le_of_norm_le hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hg t ht))
  calc
    ‖∫ t in Set.Ioi R, g t‖ ≤ ∫ t in Set.Ioi R, A * t ^ a := hle
    _ = A * (∫ t in Set.Ioi R, t ^ a) := by rw [MeasureTheory.integral_const_mul]
    _ = A * (-R ^ (a + 1) / (a + 1)) := by rw [integral_Ioi_rpow_of_lt ha hR]

/-- A square-root majorant of the integrand past the conductor scale has a
bound independent of the conductor and of `σ ∈ [1, 2]`. -/
theorem norm_integral_Ioi_le_four_mul (g : ℝ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ₁ : 1 ≤ σ)
    (hg : ∀ t, Q < t →
      ‖g t‖ ≤ 2 * C * Q ^ (1 / 2 : ℝ) * t ^ (-σ - 1 / 2)) :
    ‖∫ t in Set.Ioi Q, g t‖ ≤ 4 * C := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hexp : -σ - (1 / 2 : ℝ) < -1 := by linarith
  have hbase := norm_integral_Ioi_le_rpow g
    (2 * C * Q ^ (1 / 2 : ℝ)) (-σ - 1 / 2) Q hexp hQpos hg
  have hpow : Q ^ (1 / 2 : ℝ) * Q ^ ((1 / 2 : ℝ) - σ) =
      Q ^ (1 - σ) := by
    rw [← Real.rpow_add hQpos]
    congr 1
    ring
  have hpowle : Q ^ (1 - σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith)
  have hdpos : 0 < σ - (1 / 2 : ℝ) := by linarith
  have hvalue :
      (2 * C * Q ^ (1 / 2 : ℝ)) *
        (-Q ^ ((-σ - 1 / 2 : ℝ) + 1) / ((-σ - 1 / 2 : ℝ) + 1)) =
      (2 * C * Q ^ (1 - σ)) / (σ - 1 / 2) := by
    have heq : (-σ - (1 / 2 : ℝ)) + 1 = (1 / 2 : ℝ) - σ := by ring
    rw [heq]
    have hd : (1 / 2 : ℝ) - σ = -(σ - 1 / 2) := by ring
    rw [hd]
    calc
      2 * C * Q ^ (1 / 2 : ℝ) *
          (-Q ^ (-(σ - 1 / 2)) / -(σ - 1 / 2)) =
          (2 * C * (Q ^ (1 / 2 : ℝ) * Q ^ (-(σ - 1 / 2)))) /
            (σ - 1 / 2) := by
          simp only [neg_div_neg_eq]
          ring
      _ = (2 * C * Q ^ (1 - σ)) / (σ - 1 / 2) := by
        rw [show -(σ - (1 / 2 : ℝ)) = (1 / 2 : ℝ) - σ by ring, hpow]
  have hnum : 2 * C * Q ^ (1 - σ) ≤ 2 * C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowle (by positivity : 0 ≤ 2 * C)
  have hden : 2 * C ≤ 4 * C * (σ - 1 / 2) := by nlinarith
  calc
    ‖∫ t in Set.Ioi Q, g t‖ ≤
        (2 * C * Q ^ (1 / 2 : ℝ)) *
          (-Q ^ ((-σ - 1 / 2 : ℝ) + 1) / ((-σ - 1 / 2 : ℝ) + 1)) := hbase
    _ = (2 * C * Q ^ (1 - σ)) / (σ - 1 / 2) := hvalue
    _ ≤ 4 * C := (div_le_iff₀ hdpos).mpr (hnum.trans hden)

/-- Pointwise majorant of the Abel integrand beyond the conductor scale. -/
theorem norm_weighted_partial_sum_le (S : ℝ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q)
    (hS : ∀ t, Q < t →
      ‖S t‖ ≤ C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q))
    (t : ℝ) (ht : Q < t) :
    ‖S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ ≤
      2 * C * Q ^ (1 / 2 : ℝ) * t ^ (-σ - 1 / 2) := by
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have htpos : 0 < t := hQpos.trans ht
  have hQt : Q ≤ Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) := by
    have hsq : Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) = Q := by
      rw [← Real.rpow_add hQpos]
      norm_num
    calc
      Q = Q ^ (1 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) := hsq.symm
      _ ≤ Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hQpos.le ht.le (by norm_num)) (by positivity)
  have hwpos : 0 ≤ t ^ (-σ - 1) := Real.rpow_nonneg htpos.le _
  have hpow : t ^ (1 / 2 : ℝ) * t ^ (-σ - 1) = t ^ (-σ - 1 / 2) := by
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  calc
    ‖S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ = ‖S t‖ * t ^ (-σ - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwpos]
    _ ≤ C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q) * t ^ (-σ - 1) :=
      mul_le_mul_of_nonneg_right (hS t ht) hwpos
    _ ≤ 2 * C * Q ^ (1 / 2 : ℝ) * t ^ (-σ - 1 / 2) := by
      have hbound := mul_le_mul_of_nonneg_left hQt hC
      calc
        C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q) * t ^ (-σ - 1) ≤
            C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) +
              Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ)) * t ^ (-σ - 1) := by
          gcongr
        _ = 2 * C * Q ^ (1 / 2 : ℝ) * t ^ (-σ - 1 / 2) := by rw [← hpow]; ring

/-- The error `C (√Q √t + Q)` in a coefficient partial-sum estimate gives
the uniform tail integral bound after weighting by `t ^ (-σ-1)`. -/
theorem norm_weighted_partial_sum_integral_le_four (S : ℝ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ : 1 ≤ σ)
    (hS : ∀ t, Q < t →
      ‖S t‖ ≤ C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q)) :
    ‖∫ t in Set.Ioi Q, S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ ≤ 4 * C := by
  apply norm_integral_Ioi_le_four_mul
    (fun t => S t * ((t ^ (-σ - 1) : ℝ) : ℂ)) C Q σ hC hQ hσ
  exact norm_weighted_partial_sum_le S C Q σ hC hQ hS

/-- The same partial-sum estimate supplies integrability of Abel's
step-function integrand on `(1, ∞)` when `σ ≥ 1`. -/
theorem weighted_partial_sum_integrable (f : ℕ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ : 1 ≤ σ)
    (hFar : ∀ t, Q < t →
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤
        C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q)) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (∑ k ∈ Icc 1 ⌊t⌋₊, f k) *
        ((t ^ (-σ - 1) : ℝ) : ℂ)) (Set.Ioi 1) := by
  let S : ℝ → ℂ := fun t => ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  let g : ℝ → ℂ := fun t => S t * ((t ^ (-σ - 1) : ℝ) : ℂ)
  have hweight : ContinuousOn (fun t : ℝ => ((t ^ (-σ - 1) : ℝ) : ℂ))
      (Set.Ici 1) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    intro t ht
    exact (Real.continuousAt_rpow_const _ _
      (Or.inl (zero_lt_one.trans_le ht).ne')).continuousWithinAt
  have hloc : MeasureTheory.LocallyIntegrableOn g (Set.Ici 1) := by
    simpa only [g, S, mul_comm] using
      (locallyIntegrableOn_mul_sum_Icc f zero_le_one
        (hweight.locallyIntegrableOn measurableSet_Ici))
  have hBigO : g =O[Filter.atTop] (fun t : ℝ => t ^ (-σ - 1 / 2)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2 * C * Q ^ (1 / 2 : ℝ), ?_⟩
    filter_upwards [Filter.eventually_gt_atTop Q] with t ht
    have htpos : 0 < t := (lt_of_lt_of_le zero_lt_one hQ).trans ht
    simpa [g, S, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg htpos.le _)] using
      (norm_weighted_partial_sum_le S C Q σ hC hQ hFar t ht)
  have hpowInt : MeasureTheory.IntegrableAtFilter
      (fun t : ℝ => t ^ (-σ - 1 / 2)) Filter.atTop := by
    exact integrableAtFilter_rpow_atTop_iff.mpr (by linarith)
  exact (hloc.integrableOn_of_isBigO_atTop hBigO hpowInt).mono_set
    Set.Ioi_subset_Ici_self

/-- A reciprocal majorant on the finite interval contributes at most `C log Q`.
This applies to step functions coming from coefficient partial sums. -/
theorem norm_integral_Ioc_le_log (g : ℝ → ℂ) (C Q : ℝ)
    (hQ : 1 ≤ Q)
    (hg : ∀ t ∈ Set.Ioc (1 : ℝ) Q, ‖g t‖ ≤ C * t⁻¹) :
    ‖∫ t in Set.Ioc (1 : ℝ) Q, g t‖ ≤ C * Real.log Q := by
  have hcont : ContinuousOn (fun t : ℝ => C * t⁻¹) (Set.Icc 1 Q) :=
    continuousOn_const.mul
      (continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hInt : MeasureTheory.IntegrableOn (fun t : ℝ => C * t⁻¹) (Set.Ioc 1 Q) :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hle : ‖∫ t in Set.Ioc (1 : ℝ) Q, g t‖ ≤
      ∫ t in Set.Ioc (1 : ℝ) Q, C * t⁻¹ :=
    MeasureTheory.norm_integral_le_of_norm_le hInt
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hg)
  calc
    ‖∫ t in Set.Ioc (1 : ℝ) Q, g t‖ ≤
        ∫ t in Set.Ioc (1 : ℝ) Q, C * t⁻¹ := hle
    _ = C * ∫ t in (1 : ℝ)..Q, t⁻¹ := by
      rw [← intervalIntegral.integral_of_le hQ, intervalIntegral.integral_const_mul]
    _ = C * Real.log Q := by rw [integral_inv_of_pos zero_lt_one (by linarith : 0 < Q)]; simp

/-- The linear bound on cumulative absolute coefficients gives the logarithmic
part of Abel's integral, uniformly for `σ ≥ 1`. -/
theorem norm_weighted_partial_sum_integral_le_log (S : ℝ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ : 1 ≤ σ)
    (hS : ∀ t ∈ Set.Ioc (1 : ℝ) Q, ‖S t‖ ≤ C * t) :
    ‖∫ t in Set.Ioc (1 : ℝ) Q,
      S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ ≤ C * Real.log Q := by
  apply norm_integral_Ioc_le_log
    (fun t => S t * ((t ^ (-σ - 1) : ℝ) : ℂ)) C Q hQ
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1.le
  have htone : (1 : ℝ) ≤ t := ht.1.le
  have hwpos : 0 ≤ t ^ (-σ - 1) := Real.rpow_nonneg htpos.le _
  have hpow : t * t ^ (-σ - 1) = t ^ (-σ) := by
    nth_rewrite 1 [← Real.rpow_one t]
    rw [← Real.rpow_add htpos]
    congr 1
    ring
  calc
    ‖S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ = ‖S t‖ * t ^ (-σ - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwpos]
    _ ≤ C * t * t ^ (-σ - 1) := mul_le_mul_of_nonneg_right (hS t ht) hwpos
    _ = C * t ^ (-σ) := by rw [mul_assoc, hpow]
    _ ≤ C * t ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le htone (by linarith)) hC
    _ = C * t⁻¹ := by rw [Real.rpow_neg_one]

/-- Combining the two regions of Abel's integral. The only extra premise is
integrability of the step-function integrand on `(1, ∞)`. -/
theorem norm_abel_integral_le_log_add_four (S : ℝ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ : 1 ≤ σ)
    (hInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => S t * ((t ^ (-σ - 1) : ℝ) : ℂ)) (Set.Ioi 1))
    (hNear : ∀ t ∈ Set.Ioc (1 : ℝ) Q, ‖S t‖ ≤ C * t)
    (hFar : ∀ t, Q < t →
      ‖S t‖ ≤ C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q)) :
    ‖∫ t in Set.Ioi (1 : ℝ), S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ ≤
      C * Real.log Q + 4 * C := by
  let g : ℝ → ℂ := fun t => S t * ((t ^ (-σ - 1) : ℝ) : ℂ)
  have hsplit : (∫ t in Set.Ioc (1 : ℝ) Q, g t) +
      (∫ t in Set.Ioi Q, g t) = ∫ t in Set.Ioi (1 : ℝ), g t := by
    simpa only [intervalIntegral.integral_of_le hQ] using
      (intervalIntegral.integral_interval_add_Ioi hInt
        (hInt.mono_set (Set.Ioi_subset_Ioi hQ)))
  rw [← hsplit]
  exact (norm_add_le _ _).trans <|
    add_le_add
      (norm_weighted_partial_sum_integral_le_log S C Q σ hC hQ hσ hNear)
      (norm_weighted_partial_sum_integral_le_four S C Q σ hC hQ hσ hFar)

/-- Conditional uniform logarithmic estimate for a real L-series value.
The hypotheses are the cumulative absolute count and the conductor-scale
cancellation estimate, expressed directly for the coefficient partial-sum
step function. The `IsBigO` and integrability premises make the Abel
representation available; these follow from the same estimates in the
concrete Gaussian application. -/
theorem norm_LSeries_le_two_log_add_eight (f : ℕ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖f k‖) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)))
    (hInt : MeasureTheory.IntegrableOn
      (fun t : ℝ => (∑ k ∈ Icc 1 ⌊t⌋₊, f k) *
        ((t ^ (-σ - 1) : ℝ) : ℂ)) (Set.Ioi 1))
    (hNear : ∀ t ∈ Set.Ioc (1 : ℝ) Q,
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤ C * t)
    (hFar : ∀ t, Q < t →
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤
        C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q)) :
    ‖LSeries f (σ : ℂ)‖ ≤ 2 * C * Real.log Q + 8 * C := by
  let S : ℝ → ℂ := fun t => ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  have hrepr := LSeries_eq_mul_integral' f (r := (1 : ℝ)) (s := (σ : ℂ)) (by norm_num)
    (by simpa using hσ₁) hO
  have hconvert :
      (∫ t in Set.Ioi (1 : ℝ), S t * (t : ℂ) ^ (-((σ : ℂ) + 1))) =
      ∫ t in Set.Ioi (1 : ℝ), S t * ((t ^ (-σ - 1) : ℝ) : ℂ) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans ht
    have hexp : -((σ : ℂ) + 1) = ((-σ - 1 : ℝ) : ℂ) := by push_cast; ring
    change S t * (t : ℂ) ^ (-((σ : ℂ) + 1)) = S t * ((t ^ (-σ - 1) : ℝ) : ℂ)
    rw [hexp, Complex.ofReal_cpow htpos.le]
  have hbound := norm_abel_integral_le_log_add_four S C Q σ hC hQ hσ₁.le
    hInt hNear hFar
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  calc
    ‖LSeries f (σ : ℂ)‖ =
        σ * ‖∫ t in Set.Ioi (1 : ℝ), S t * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ := by
      rw [hrepr, hconvert, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ σ)]
    _ ≤ σ * (C * Real.log Q + 4 * C) :=
      mul_le_mul_of_nonneg_left hbound (by linarith)
    _ ≤ 2 * (C * Real.log Q + 4 * C) :=
      mul_le_mul_of_nonneg_right hσ₂ (by positivity)
    _ = 2 * C * Real.log Q + 8 * C := by ring

/-- A uniform logarithmic L-series bound from the two explicit coefficient
estimates used for Gaussian Hecke characters. The cumulative absolute bound
comes from counting lattice points; the second bound is the cancellation
estimate at conductor scale. -/
theorem norm_LSeries_le_log_of_partial_sum_bounds (f : ℕ → ℂ) (C Q σ : ℝ)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hAbs : ∀ n, (∑ k ∈ Icc 1 n, ‖f k‖) ≤ C * n)
    (hCancel : ∀ t, Q < t →
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤
        C * (Q ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + Q)) :
    ‖LSeries f (σ : ℂ)‖ ≤ 2 * C * Real.log Q + 8 * C := by
  have hNear : ∀ t ∈ Set.Ioc (1 : ℝ) Q,
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤ C * t := by
    intro t ht
    have htpos : 0 ≤ t := le_trans zero_le_one ht.1.le
    calc
      ‖∑ k ∈ Icc 1 ⌊t⌋₊, f k‖ ≤ ∑ k ∈ Icc 1 ⌊t⌋₊, ‖f k‖ := norm_sum_le _ _
      _ ≤ C * (⌊t⌋₊ : ℝ) := hAbs _
      _ ≤ C * t := mul_le_mul_of_nonneg_left (Nat.floor_le htpos) hC
  exact norm_LSeries_le_two_log_add_eight f C Q σ hC hQ hσ₁ hσ₂
    (sum_norm_isBigO_natCast f C hAbs)
    (weighted_partial_sum_integrable f C Q σ hC hQ hσ₁.le hCancel)
    hNear hCancel

end Erdos940.Quartic.GaussianLBoundAnalytic
