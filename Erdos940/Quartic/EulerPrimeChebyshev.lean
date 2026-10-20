import Erdos940.Quartic.EulerLogComparison
import Erdos940.Quartic.EulerProductInequality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Chebyshev estimates for Euler-log comparison

The rational-prime estimates behind the bounded smoothing and tail errors.
Gaussian prime-ideal sums will be obtained from these by the splitting
classification: at most two norm-`p` ideals and at most one norm-`p²` ideal
over each rational prime.
-/

namespace Erdos940.Quartic

open Finset MeasureTheory intervalIntegral

noncomputable def rationalPrimeLogSum (B : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE B, Real.log p / (p : ℝ)

private theorem reciprocal_deriv_integrable (B : ℝ) :
    IntegrableOn (deriv fun x : ℝ => x⁻¹) (Set.Icc 2 B) := by
  rw [deriv_inv']
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero _ hx0
  exact ((continuousAt_id.pow 2).inv₀ hx2).neg.continuousWithinAt

theorem rationalPrimeLogSum_eq_theta_integral (B : ℝ) (hB : 2 ≤ B) :
    rationalPrimeLogSum ⌊B⌋₊ =
      Chebyshev.theta B / B +
        ∫ t in 2..B, Chebyshev.theta t / t ^ 2 := by
  classical
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n => Real.log n)
  have hsum : rationalPrimeLogSum ⌊B⌋₊ =
      ∑ n ∈ Finset.Icc 0 ⌊B⌋₊, (n : ℝ)⁻¹ * a n := by
    simp only [rationalPrimeLogSum, Nat.primesLE_eq_filter_Icc_zero,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [a, hp, div_eq_mul_inv, mul_comm]
    · simp [a, hp]
  rw [hsum, sum_mul_eq_sub_integral_mul₁ a (f := fun x : ℝ => x⁻¹)
    (by simp [a]) (by simp [a]) B (by
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      fun_prop) (reciprocal_deriv_integrable B)]
  have hsumTheta (x : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, a n) = Chebyshev.theta x := by
    simp [a, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      Set.indicator_apply]
  rw [hsumTheta B]
  rw [← intervalIntegral.integral_of_le hB]
  rw [show (fun t : ℝ => deriv (fun x : ℝ => x⁻¹) t *
      ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) =
      (fun t : ℝ => -(Chebyshev.theta t / t ^ 2)) from by
      funext t
      rw [hsumTheta]
      simp [deriv_inv', div_eq_mul_inv, mul_comm]]
  simp [intervalIntegral.integral_neg, div_eq_mul_inv, mul_comm]

private theorem theta_div_sq_integrable (B : ℝ) :
    IntegrableOn (fun t : ℝ => Chebyshev.theta t / t ^ 2)
      (Set.Icc 2 B) volume := by
  conv => arg 1; ext t; rw [Chebyshev.theta_eq_sum_Icc, div_eq_mul_one_div,
    mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) ?_
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht0
  convert ((continuousAt_id.pow 2).inv₀ ht2).continuousWithinAt using 1
  funext u
  simp [one_div]

/-- The Chebyshev theta bound gives the logarithmic smoothing estimate
needed in `EulerLogComparison`. -/
theorem rationalPrimeLogSum_le (B : ℝ) (hB : 2 ≤ B) :
    rationalPrimeLogSum ⌊B⌋₊ ≤
      Real.log 4 * (1 + Real.log B) := by
  have hBpos : 0 < B := by linarith
  have hTheta := Chebyshev.theta_le_log4_mul_x hBpos.le
  have hfirst : Chebyshev.theta B / B ≤ Real.log 4 := by
    exact (div_le_iff₀ hBpos).2 (by simpa [mul_comm] using hTheta)
  have hInt :
      (∫ t in 2..B, Chebyshev.theta t / t ^ 2) ≤
        ∫ t in 2..B, Real.log 4 / t := by
    apply intervalIntegral.integral_mono_on hB
    · apply intervalIntegrable_iff.mpr
      rw [Set.uIoc_of_le hB, ← integrableOn_Icc_iff_integrableOn_Ioc]
      exact theta_div_sq_integrable B
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      have ht' : t ∈ Set.Icc 2 B := by simpa [Set.uIcc_of_le hB] using ht
      have ht0 : t ≠ 0 := by linarith [ht'.1]
      exact continuousWithinAt_const.div
        continuousWithinAt_id ht0
    · intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      have htTheta := Chebyshev.theta_le_log4_mul_x htpos.le
      have hsq : 0 < t ^ 2 := pow_pos htpos _
      apply (div_le_div_iff₀ hsq htpos).2
      nlinarith [htTheta]
  have hIntegral : (∫ t in 2..B, Real.log 4 / t) ≤
      Real.log 4 * Real.log B := by
    rw [show (fun t : ℝ => Real.log 4 / t) =
        (fun t : ℝ => Real.log 4 * t⁻¹) from by funext t; ring,
      intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by norm_num) hBpos,
      Real.log_div (by positivity : B ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  rw [rationalPrimeLogSum_eq_theta_integral B hB]
  linarith

/-- A scale-invariant form matching the Chebyshev-below premise of
`finite_prime_sum_le_logL`. -/
theorem rationalPrimeLogSum_le_mul_log (B : ℝ) (hB : 2 ≤ B) :
    rationalPrimeLogSum ⌊B⌋₊ ≤
      (Real.log 4 * (1 + 1 / Real.log 2)) * Real.log B := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogB : Real.log 2 ≤ Real.log B :=
    Real.log_le_log (by norm_num) hB
  have hBscale : 1 ≤ Real.log B / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogB)
  have hfirst := rationalPrimeLogSum_le B hB
  have hineq : Real.log 4 * (1 + Real.log B) ≤
      (Real.log 4 * (1 + 1 / Real.log 2)) * Real.log B := by
    have : Real.log 4 * (1 + Real.log B) ≤
        Real.log 4 * (Real.log B / Real.log 2 + Real.log B) :=
      mul_le_mul_of_nonneg_left (by linarith) hlog4
    calc
      _ ≤ Real.log 4 * (Real.log B / Real.log 2 + Real.log B) := this
      _ = _ := by ring
  exact hfirst.trans hineq

/-- A weighted Chebyshev prime sum, before taking the infinite tail. -/
noncomputable def rationalPrimeWeightedSum (X sigma : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊X⌋₊,
    Real.log p / (p : ℝ) ^ sigma

theorem rationalPrimeWeightedSum_eq_theta_integral
    (X sigma : ℝ) (hX : 2 ≤ X) :
    rationalPrimeWeightedSum X sigma =
      Chebyshev.theta X / X ^ sigma +
        sigma * ∫ t in 2..X, Chebyshev.theta t / t ^ (sigma + 1) := by
  classical
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n => Real.log n)
  have hsum : rationalPrimeWeightedSum X sigma =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (n : ℝ) ^ (-sigma) * a n := by
    simp only [rationalPrimeWeightedSum, Nat.primesLE_eq_filter_Icc_zero,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [a, hp, Real.rpow_neg, div_eq_mul_inv, mul_comm]
    · simp [a, hp]
  have hderivInt : IntegrableOn
      (deriv fun t : ℝ => t ^ (-sigma)) (Set.Icc 2 X) volume := by
    rw [Real.deriv_rpow_const']
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact continuousWithinAt_const.mul
      ((continuousAt_id.rpow_const (Or.inl ht0)).continuousWithinAt)
  have hsumTheta (t : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) = Chebyshev.theta t := by
    simp [a, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter,
      Set.indicator_apply]
  rw [hsum, sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ => t ^ (-sigma))
    (by simp [a]) (by simp [a]) X (by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      exact Real.differentiableAt_rpow_const_of_ne _ ht0) hderivInt]
  rw [hsumTheta X, ← intervalIntegral.integral_of_le hX]
  rw [show (fun t : ℝ => deriv (fun u : ℝ => u ^ (-sigma)) t *
      ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n) =
      (fun t : ℝ => -sigma * (Chebyshev.theta t / t ^ (sigma + 1))) from by
      funext t
      rw [hsumTheta, Real.deriv_rpow_const]
      by_cases htpos : 0 < t
      · have hexp : -sigma - 1 = -(sigma + 1) := by ring
        rw [hexp, Real.rpow_neg htpos.le]
        ring
      · have htheta : Chebyshev.theta t = 0 :=
          Chebyshev.theta_eq_zero_of_le_one (by linarith)
        simp [htheta]]
  rw [intervalIntegral.integral_const_mul]
  rw [Real.rpow_neg (by linarith : 0 ≤ X) sigma]
  simp [div_eq_mul_inv]
  ring

private theorem theta_div_rpow_integrable (X sigma : ℝ) :
    IntegrableOn (fun t : ℝ => Chebyshev.theta t / t ^ (sigma + 1))
      (Set.Icc 2 X) volume := by
  conv => arg 1; ext t; rw [Chebyshev.theta_eq_sum_Icc, div_eq_mul_one_div,
    mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) ?_
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hpow : t ^ (sigma + 1) ≠ 0 :=
    (Real.rpow_pos_of_pos (show 0 < t by linarith [ht.1]) _).ne'
  convert ((continuousAt_id.rpow_const (p := sigma + 1) (Or.inl ht0)).inv₀
    hpow).continuousWithinAt using 1
  funext u
  simp [one_div]

/-- The weighted prime sum has the uniform `1/(sigma-1)` bound directly
from Chebyshev's theta inequality. -/
theorem rationalPrimeWeightedSum_le (X sigma : ℝ)
    (hX : 2 ≤ X) (hsigma : 1 < sigma) :
    rationalPrimeWeightedSum X sigma ≤
      Real.log 4 * (1 + sigma / (sigma - 1)) := by
  have hXpos : 0 < X := by linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hfirst : Chebyshev.theta X / X ^ sigma ≤ Real.log 4 := by
    have htheta := Chebyshev.theta_le_log4_mul_x hXpos.le
    have hpow : 0 < X ^ sigma := Real.rpow_pos_of_pos hXpos _
    have hpowle : X ^ (1 - sigma) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc
      Chebyshev.theta X / X ^ sigma ≤
          Real.log 4 * X / X ^ sigma :=
        div_le_div_of_nonneg_right htheta hpow.le
      _ = Real.log 4 * X ^ (1 - sigma) := by
        rw [Real.rpow_sub hXpos]
        simp only [Real.rpow_one, div_eq_mul_inv]
        ring
      _ ≤ Real.log 4 := by nlinarith
  have hInt :
      (∫ t in 2..X, Chebyshev.theta t / t ^ (sigma + 1)) ≤
        Real.log 4 * ∫ t in 2..X, t ^ (-sigma) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hX
    · apply intervalIntegrable_iff.mpr
      rw [Set.uIoc_of_le hX, ← integrableOn_Icc_iff_integrableOn_Ioc]
      exact theta_div_rpow_integrable X sigma
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      have ht' : t ∈ Set.Icc 2 X := by simpa [Set.uIcc_of_le hX] using ht
      have ht0 : t ≠ 0 := by linarith [ht'.1]
      exact continuousWithinAt_const.mul
        ((continuousAt_id.rpow_const (Or.inl ht0)).continuousWithinAt)
    · intro t ht
      have ht' : t ∈ Set.Icc 2 X := by simpa [Set.uIcc_of_le hX] using ht
      have htpos : 0 < t := by linarith [ht'.1]
      have htheta := Chebyshev.theta_le_log4_mul_x htpos.le
      have hpow : 0 < t ^ (sigma + 1) := Real.rpow_pos_of_pos htpos _
      calc
        Chebyshev.theta t / t ^ (sigma + 1) ≤
            Real.log 4 * t / t ^ (sigma + 1) :=
          div_le_div_of_nonneg_right htheta hpow.le
        _ = Real.log 4 * t ^ (-sigma) := by
          rw [Real.rpow_add htpos, Real.rpow_one, Real.rpow_neg htpos.le]
          field_simp
  have hIntegral : (∫ t in 2..X, t ^ (-sigma)) ≤ 1 / (sigma - 1) := by
    have hσ : 0 < sigma - 1 := by linarith
    have hnot : (0 : ℝ) ∉ Set.uIcc 2 X := by
      rw [Set.uIcc_of_le hX]
      simp
    rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩)]
    have hXpow : 0 ≤ X ^ (1 - sigma) := Real.rpow_nonneg hXpos.le _
    have h2pow : (2 : ℝ) ^ (1 - sigma) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hform :
        (X ^ (-sigma + 1) - (2 : ℝ) ^ (-sigma + 1)) / (-sigma + 1) =
          ((2 : ℝ) ^ (1 - sigma) - X ^ (1 - sigma)) / (sigma - 1) := by
      have hexp : -sigma + 1 = 1 - sigma := by ring
      rw [hexp]
      have hden : 1 - sigma = -(sigma - 1) := by ring
      rw [hden, div_neg]
      ring
    rw [hform]
    exact (div_le_div_iff₀ hσ hσ).2 (by nlinarith)
  rw [rationalPrimeWeightedSum_eq_theta_integral X sigma hX]
  have hσ : 0 ≤ sigma := by linarith
  have hInt2 := mul_le_mul_of_nonneg_left hInt hσ
  have hInt3 := mul_le_mul_of_nonneg_left hIntegral
    (mul_nonneg hσ hlog4)
  have hId : Real.log 4 * (1 + sigma / (sigma - 1)) =
      Real.log 4 + sigma * (Real.log 4 * (1 / (sigma - 1))) := by ring
  rw [hId]
  linarith

/-- Any finite tail of rational primes has bounded smoothed mass. The
bound is independent of the size and position of the finite tail. -/
theorem rationalPrimeFiniteTail_le (B sigma : ℝ) (hB : 2 ≤ B)
    (hsigma : 1 < sigma) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ B < (p : ℝ)) :
    (∑ p ∈ F, (1 : ℝ) / (p : ℝ) ^ sigma) ≤
      (Real.log 4 * (1 + sigma / (sigma - 1))) / Real.log B := by
  have hlogB : 0 < Real.log B :=
    Real.log_pos (by linarith)
  let N : ℕ := max 2 (F.sup id)
  have hN : 2 ≤ N := le_max_left _ _
  have hsub : F ⊆ Nat.primesLE N := by
    intro p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, (hF p hp).1⟩
    exact (Finset.le_sup (f := id) hp).trans (le_max_right _ _)
  have hterm (p : ℕ) (hp : p ∈ F) :
      (1 : ℝ) / (p : ℝ) ^ sigma ≤
        (Real.log p / (p : ℝ) ^ sigma) / Real.log B := by
    have hpReal : (0 : ℝ) < p := (hF p hp).2.trans' (by linarith)
    have hpow : 0 < (p : ℝ) ^ sigma := Real.rpow_pos_of_pos hpReal _
    have hlogle : Real.log B ≤ Real.log p :=
      Real.log_le_log (by linarith) (hF p hp).2.le
    have hnum : (1 : ℝ) / (p : ℝ) ^ sigma ≤
        Real.log p / (p : ℝ) ^ sigma / Real.log B := by
      apply (div_le_div_iff₀ hpow hlogB).2
      field_simp
      nlinarith
    exact hnum
  have hsum : (∑ p ∈ F, (1 : ℝ) / (p : ℝ) ^ sigma) ≤
      (∑ p ∈ F, Real.log p / (p : ℝ) ^ sigma) / Real.log B := by
    calc
      _ ≤ ∑ p ∈ F, (Real.log p / (p : ℝ) ^ sigma) / Real.log B :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_div]
  have hweighted :
      (∑ p ∈ F, Real.log p / (p : ℝ) ^ sigma) ≤
        rationalPrimeWeightedSum (N : ℝ) sigma := by
    change (∑ p ∈ F, Real.log p / (p : ℝ) ^ sigma) ≤
      ∑ p ∈ Nat.primesLE ⌊(N : ℝ)⌋₊,
        Real.log p / (p : ℝ) ^ sigma
    rw [Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    positivity
  have hlimit := rationalPrimeWeightedSum_le (N : ℝ) sigma
    (by exact_mod_cast hN) hsigma
  exact hsum.trans ((div_le_div_of_nonneg_right
    (hweighted.trans hlimit) hlogB.le))

/-- The rational-prime tail mass at `sigma = 1 + 1/log B` has an absolute
bound independent of the cutoff and the selected finite subset. -/
theorem rationalPrimeFiniteSmoothedTail_le (B : ℝ) (hB : 2 ≤ B)
    (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime ∧ B < (p : ℝ)) :
    (∑ p ∈ F, eulerMassTerm (fun p : ℕ => (p : ℝ)) B p) ≤
      Real.log 4 * (1 + 2 / Real.log 2) := by
  let sigma : ℝ := 1 + 1 / Real.log B
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log B :=
    Real.log_le_log (by norm_num) hB
  have hsigma : 1 < sigma := by
    dsimp [sigma]
    exact lt_add_of_pos_right _ (one_div_pos.mpr hlogB)
  have hterm (p : ℕ) (hp : p ∈ F) :
      eulerMassTerm (fun p : ℕ => (p : ℝ)) B p =
        (1 : ℝ) / (p : ℝ) ^ sigma := by
    have hpPos : (0 : ℝ) < p := by
      have := (hF p hp).1.pos
      exact_mod_cast this
    simpa [eulerMassTerm, eulerSmoothedTerm, sigma] using
      (eulerSmoothedTerm_eq_power (fun p : ℕ => (p : ℝ))
        (fun _ => (1 : ℝ)) B p hpPos)
  have hfirst :
      (∑ p ∈ F, eulerMassTerm (fun p : ℕ => (p : ℝ)) B p) ≤
        (Real.log 4 * (1 + sigma / (sigma - 1))) / Real.log B := by
    calc
      _ = ∑ p ∈ F, (1 : ℝ) / (p : ℝ) ^ sigma :=
        Finset.sum_congr rfl hterm
      _ ≤ _ := rationalPrimeFiniteTail_le B sigma hB hsigma F hF
  have hident :
      (Real.log 4 * (1 + sigma / (sigma - 1))) / Real.log B =
        Real.log 4 * (1 + 2 / Real.log B) := by
    dsimp [sigma]
    field_simp
    ring
  rw [hident] at hfirst
  have hinv : 1 / Real.log B ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 hlogle
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcore : 1 + 2 / Real.log B ≤ 1 + 2 / Real.log 2 := by
    linear_combination 2 * hinv
  exact hfirst.trans (mul_le_mul_of_nonneg_left hcore hlog4)

/-- The exact unsigned-tail premise of `eulerTail_lower_of_mass` for a
rational-prime index system. The finite set must contain every prime of norm
at most `B`; no condition is placed on any additional primes it contains. -/
theorem rationalPrimeTailMass_le (B : ℝ) (hB : 2 ≤ B)
    (S : Finset Nat.Primes)
    (hS : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ)) :
    (∑' P : (Sᶜ : Set Nat.Primes),
      eulerMassTerm (fun P : Nat.Primes => (P : ℝ)) B P) ≤
        Real.log 4 * (1 + 2 / Real.log 2) := by
  classical
  apply Real.tsum_le_of_sum_le (fun _ => by
    unfold eulerMassTerm
    positivity)
  intro u
  let f : (Sᶜ : Set Nat.Primes) → ℕ := fun P => P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hF : ∀ p ∈ u.image f, p.Prime ∧ B < (p : ℝ) := by
    intro p hp
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨P.val.property, ?_⟩
    exact hS P.val P.property
  calc
    (∑ P ∈ u, eulerMassTerm (fun P : Nat.Primes => (P : ℝ)) B P) =
        ∑ p ∈ u.image f,
          eulerMassTerm (fun p : ℕ => (p : ℝ)) B p := by
      rw [Finset.sum_image (fun P _ Q _ h => hf h)]
      rfl
    _ ≤ Real.log 4 * (1 + 2 / Real.log 2) :=
      rationalPrimeFiniteSmoothedTail_le B hB (u.image f) hF

/-- Count a finite family by its fibers over rational primes. -/
theorem sum_over_prime_fibers_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (w : Nat.Primes → ℝ)
    (m : ℕ) (hw : ∀ p, 0 ≤ w p)
    (hm : ∀ p : Nat.Primes,
      (F.filter fun i => base i = p).card ≤ m) :
    (∑ i ∈ F, w (base i)) ≤ m * ∑ p ∈ F.image base, w p := by
  classical
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    F (F.image base) base (fun i => w (base i))
  have hfilter : (F.filter fun i => base i ∈ F.image base) = F := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hi
      exact ⟨hi, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  rw [hfilter] at hfiber
  have hinner (p : Nat.Primes) :
      (∑ i ∈ F.filter (fun i => base i = p), w (base i)) =
        ((F.filter fun i => base i = p).card : ℝ) * w p := by
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2])]
    simp
  calc
    (∑ i ∈ F, w (base i)) =
        ∑ p ∈ F.image base,
          (∑ i ∈ F.filter (fun i => base i = p), w (base i)) := hfiber.symm
    _ = ∑ p ∈ F.image base,
          ((F.filter fun i => base i = p).card : ℝ) * w p := by
      apply Finset.sum_congr rfl
      intro p _
      exact hinner p
    _ ≤ ∑ p ∈ F.image base, (m : ℝ) * w p := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm p) (hw p)
    _ = m * ∑ p ∈ F.image base, w p := by rw [Finset.mul_sum]

/-- At most two norm-`p` Gaussian ideals lie above each rational prime.
This abstract theorem only asks for that fiber bound; an application to
Gaussian prime ideals supplies the splitting classification separately. -/
theorem gaussianDegreeOneLogSum_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (B : ℝ)
    (hbelow : ∀ P ∈ F, (base P : ℝ) ≤ B)
    (hfiber : ∀ p : Nat.Primes,
      (F.filter fun P => base P = p).card ≤ 2) :
    (∑ P ∈ F, Real.log (base P : ℝ) / (base P : ℝ)) ≤
      2 * rationalPrimeLogSum ⌊B⌋₊ := by
  classical
  let w : Nat.Primes → ℝ := fun p => Real.log (p : ℝ) / (p : ℝ)
  have hw : ∀ p : Nat.Primes, 0 ≤ w p := by
    intro p
    unfold w
    positivity
  have hfiber := sum_over_prime_fibers_le F base w 2 hw hfiber
  have hsub : (F.image base).image (fun p : Nat.Primes => p.val) ⊆
      Nat.primesLE ⌊B⌋₊ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, (base P).property⟩
    exact Nat.le_floor (hbelow P hP)
  have hinj : Function.Injective (fun p : Nat.Primes => p.val) := Subtype.val_injective
  have hsum : (∑ p ∈ F.image base, w p) ≤ rationalPrimeLogSum ⌊B⌋₊ := by
    unfold rationalPrimeLogSum
    calc
      (∑ p ∈ F.image base, w p) =
          ∑ p ∈ (F.image base).image (fun p : Nat.Primes => p.val),
            Real.log p / (p : ℝ) := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
      _ ≤ ∑ p ∈ Nat.primesLE ⌊B⌋₊,
          Real.log p / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        positivity
  exact hfiber.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

/-- The degree-one part of the Gaussian prime-ideal tail has at most two
ideals over each rational prime. This is the finite-sum form, which can be
used with `Real.tsum_le_of_sum_le` for an infinite ideal family. -/
theorem gaussianDegreeOneFiniteSmoothedTail_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (habove : ∀ P ∈ F, B < (base P : ℝ))
    (hfiber : ∀ p : Nat.Primes,
      (F.filter fun P => base P = p).card ≤ 2) :
    (∑ P ∈ F, eulerMassTerm (fun P : ι => (base P : ℝ)) B P) ≤
      2 * (Real.log 4 * (1 + 2 / Real.log 2)) := by
  classical
  let w : Nat.Primes → ℝ :=
    fun p => eulerMassTerm (fun p : Nat.Primes => (p : ℝ)) B p
  have hw : ∀ p : Nat.Primes, 0 ≤ w p := by
    intro p
    unfold w eulerMassTerm
    positivity
  have hfiber' := sum_over_prime_fibers_le F base w 2 hw hfiber
  have hinj : Function.Injective (fun p : Nat.Primes => p.val) :=
    Subtype.val_injective
  have hF : ∀ p ∈ (F.image base).image (fun p : Nat.Primes => p.val),
      p.Prime ∧ B < (p : ℝ) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(base P).property, habove P hP⟩
  have hsum : (∑ p ∈ F.image base, w p) ≤
      Real.log 4 * (1 + 2 / Real.log 2) := by
    calc
      (∑ p ∈ F.image base, w p) =
          ∑ p ∈ (F.image base).image (fun p : Nat.Primes => p.val),
            eulerMassTerm (fun p : ℕ => (p : ℝ)) B p := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
        rfl
      _ ≤ Real.log 4 * (1 + 2 / Real.log 2) :=
        rationalPrimeFiniteSmoothedTail_le B hB _ hF
  exact hfiber'.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

/-- Degree-two Gaussian prime ideals have norm `p²`; their smoothed
tail is dominated by the convergent rational reciprocal-square series.
The splitting theorem enters only through the one-ideal-per-prime fiber
bound. -/
theorem gaussianDegreeTwoFiniteSmoothedTail_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hfiber : ∀ p : Nat.Primes,
      (F.filter fun P => base P = p).card ≤ 1) :
    (∑ P ∈ F,
      eulerMassTerm (fun P : ι => (base P : ℝ) ^ 2) B P) ≤
        reciprocalSquareConstant := by
  classical
  let w : Nat.Primes → ℝ :=
    fun p => eulerMassTerm (fun p : Nat.Primes => (p : ℝ) ^ 2) B p
  have hw : ∀ p : Nat.Primes, 0 ≤ w p := by
    intro p
    unfold w eulerMassTerm
    positivity
  have hterm (p : Nat.Primes) : w p ≤ 1 / (p : ℝ) ^ 2 := by
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
    have hnorm : 0 < (p : ℝ) ^ 2 := by positivity
    have hlognorm : 0 ≤ Real.log ((p : ℝ) ^ 2) :=
      Real.log_nonneg (by nlinarith)
    have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
    have hexp : Real.exp (-(Real.log ((p : ℝ) ^ 2) / Real.log B)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr
        (div_nonneg hlognorm hlogB.le))
    calc
      w p = (1 / (p : ℝ) ^ 2) *
          Real.exp (-(Real.log ((p : ℝ) ^ 2) / Real.log B)) := rfl
      _ ≤ (1 / (p : ℝ) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 1 / (p : ℝ) ^ 2 := by ring
  have hfiber' := sum_over_prime_fibers_le F base w 1 hw hfiber
  have hinj : Function.Injective (fun p : Nat.Primes => p.val) :=
    Subtype.val_injective
  have hsum : (∑ p ∈ F.image base, w p) ≤ reciprocalSquareConstant := by
    calc
      (∑ p ∈ F.image base, w p) ≤
          ∑ p ∈ F.image base, (1 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum (fun p _ => hterm p)
      _ = ∑ p ∈ (F.image base).image (fun p : Nat.Primes => p.val),
          (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.sum_image (fun p _ q _ h => hinj h)]
      _ ≤ reciprocalSquareConstant := finite_reciprocalSquares_le _
  change (∑ P ∈ F, w (base P)) ≤ reciprocalSquareConstant
  exact hfiber'.trans (by simpa using hsum)

/-- A coarse Chebyshev-below estimate for the degree-two Gaussian ideals.
It suffices for the uniform Euler-log error; the convergent `p⁻²` bound
above is sharper for the tail. -/
theorem gaussianDegreeTwoLogSum_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (B : ℝ)
    (hbelow : ∀ P ∈ F, (base P : ℝ) ^ 2 ≤ B)
    (hfiber : ∀ p : Nat.Primes,
      (F.filter fun P => base P = p).card ≤ 1) :
    (∑ P ∈ F,
      Real.log ((base P : ℝ) ^ 2) / (base P : ℝ) ^ 2) ≤
        4 * rationalPrimeLogSum ⌊B⌋₊ := by
  have hbase : ∀ P ∈ F, (base P : ℝ) ≤ B := by
    intro P hP
    have hp : (2 : ℝ) ≤ base P := by
      exact_mod_cast (base P).property.two_le
    nlinarith [hbelow P hP]
  have hfiber2 : ∀ p : Nat.Primes,
      (F.filter fun P => base P = p).card ≤ 2 := by
    intro p
    exact (hfiber p).trans (by norm_num)
  have hdegreeOne := gaussianDegreeOneLogSum_le F base B hbase hfiber2
  have hterm (P : ι) (hP : P ∈ F) :
      Real.log ((base P : ℝ) ^ 2) / (base P : ℝ) ^ 2 ≤
        2 * (Real.log (base P : ℝ) / (base P : ℝ)) := by
    have hp : (2 : ℝ) ≤ base P := by
      exact_mod_cast (base P).property.two_le
    have hp0 : (0 : ℝ) < base P := by linarith
    have hp1 : (1 : ℝ) ≤ base P := by linarith
    have hlog : 0 ≤ Real.log (base P : ℝ) := Real.log_nonneg hp1
    have hinv : (1 : ℝ) / (base P : ℝ) ^ 2 ≤
        1 / (base P : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hp0).mpr
      nlinarith
    calc
      Real.log ((base P : ℝ) ^ 2) / (base P : ℝ) ^ 2 =
          (2 * Real.log (base P : ℝ)) *
            (1 / (base P : ℝ) ^ 2) := by
        rw [Real.log_pow]
        ring
      _ ≤ (2 * Real.log (base P : ℝ)) *
            (1 / (base P : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * (Real.log (base P : ℝ) / (base P : ℝ)) := by ring
  calc
    (∑ P ∈ F,
      Real.log ((base P : ℝ) ^ 2) / (base P : ℝ) ^ 2) ≤
        ∑ P ∈ F, 2 * (Real.log (base P : ℝ) / (base P : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = 2 * (∑ P ∈ F, Real.log (base P : ℝ) / (base P : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (2 * rationalPrimeLogSum ⌊B⌋₊) :=
      mul_le_mul_of_nonneg_left hdegreeOne (by norm_num)
    _ = 4 * rationalPrimeLogSum ⌊B⌋₊ := by ring

/-- The abstract norm pattern of prime ideals in `ℚ(i)`: either degree one,
with norm `p`, or degree two, with norm `p²`. -/
noncomputable def gaussianIdealNorm {ι : Type*}
    (base : ι → Nat.Primes) (degreeOne : ι → Prop) [DecidablePred degreeOne]
    (P : ι) : ℝ :=
  if degreeOne P then (base P : ℝ) else (base P : ℝ) ^ 2

/-- A Chebyshev-below bound for the full abstract Gaussian prime-ideal
system, with the splitting counts exposed as hypotheses. -/
theorem gaussianIdealLogSum_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (degreeOne : ι → Prop)
    [DecidablePred degreeOne] (B : ℝ) (hB : 2 ≤ B)
    (hbelow : ∀ P ∈ F, gaussianIdealNorm base degreeOne P ≤ B)
    (hfiber1 : ∀ p : Nat.Primes,
      ((F.filter degreeOne).filter fun P => base P = p).card ≤ 2)
    (hfiber2 : ∀ p : Nat.Primes,
      ((F.filter fun P => ¬ degreeOne P).filter fun P => base P = p).card ≤ 1) :
    (∑ P ∈ F,
      Real.log (gaussianIdealNorm base degreeOne P) /
        gaussianIdealNorm base degreeOne P) ≤
      (6 * Real.log 4 * (1 + 1 / Real.log 2)) * Real.log B := by
  classical
  have hsplit :
      (∑ P ∈ F,
        Real.log (gaussianIdealNorm base degreeOne P) /
          gaussianIdealNorm base degreeOne P) =
        (∑ P ∈ F.filter degreeOne,
          Real.log (base P : ℝ) / (base P : ℝ)) +
        (∑ P ∈ F.filter (fun P => ¬ degreeOne P),
          Real.log ((base P : ℝ) ^ 2) / (base P : ℝ) ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not F degreeOne]
    congr 1
    · apply Finset.sum_congr rfl
      intro P hP
      simp [gaussianIdealNorm, (Finset.mem_filter.mp hP).2]
    · apply Finset.sum_congr rfl
      intro P hP
      simp [gaussianIdealNorm, (Finset.mem_filter.mp hP).2]
  have hfirst := gaussianDegreeOneLogSum_le
    (F.filter degreeOne) base B
    (by
      intro P hP
      simpa [gaussianIdealNorm, (Finset.mem_filter.mp hP).2] using
        hbelow P (Finset.mem_filter.mp hP).1) hfiber1
  have hsecond := gaussianDegreeTwoLogSum_le
    (F.filter fun P => ¬ degreeOne P) base B
    (by
      intro P hP
      simpa [gaussianIdealNorm, (Finset.mem_filter.mp hP).2] using
        hbelow P (Finset.mem_filter.mp hP).1) hfiber2
  have hrational := rationalPrimeLogSum_le_mul_log B hB
  rw [hsplit]
  nlinarith

/-- The combined finite Gaussian ideal tail estimate, ready for the
`Real.tsum_le_of_sum_le` interface in `EulerLogComparison`. The only
arithmetic inputs are the degree decomposition and fiber bounds. -/
theorem gaussianFiniteSmoothedTail_le {ι : Type*}
    (F : Finset ι) (base : ι → Nat.Primes) (degreeOne : ι → Prop)
    [DecidablePred degreeOne]
    (B : ℝ) (hB : 2 ≤ B)
    (habove : ∀ P ∈ F, degreeOne P → B < (base P : ℝ))
    (hfiber1 : ∀ p : Nat.Primes,
      ((F.filter degreeOne).filter fun P => base P = p).card ≤ 2)
    (hfiber2 : ∀ p : Nat.Primes,
      ((F.filter fun P => ¬ degreeOne P).filter fun P => base P = p).card ≤ 1) :
    (∑ P ∈ F, eulerMassTerm (gaussianIdealNorm base degreeOne) B P) ≤
      2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant := by
  classical
  have hsplit :
      (∑ P ∈ F, eulerMassTerm (gaussianIdealNorm base degreeOne) B P) =
        (∑ P ∈ F.filter degreeOne,
          eulerMassTerm (fun P : ι => (base P : ℝ)) B P) +
        (∑ P ∈ F.filter (fun P => ¬ degreeOne P),
          eulerMassTerm (fun P : ι => (base P : ℝ) ^ 2) B P) := by
    rw [← Finset.sum_filter_add_sum_filter_not F degreeOne]
    congr 1
    · apply Finset.sum_congr rfl
      intro P hP
      simp [eulerMassTerm, gaussianIdealNorm, (Finset.mem_filter.mp hP).2]
    · apply Finset.sum_congr rfl
      intro P hP
      simp [eulerMassTerm, gaussianIdealNorm, (Finset.mem_filter.mp hP).2]
  rw [hsplit]
  have hfirst := gaussianDegreeOneFiniteSmoothedTail_le
    (F.filter degreeOne) base B hB
    (by
      intro P hP
      exact habove P (Finset.mem_filter.mp hP).1
        (Finset.mem_filter.mp hP).2) hfiber1
  have hsecond := gaussianDegreeTwoFiniteSmoothedTail_le
    (F.filter fun P => ¬ degreeOne P) base B hB hfiber2
  linarith

/-- A full (possibly infinite) Gaussian-prime-ideal tail bound in the
abstract degree-one/degree-two norm system. The finite-fiber hypotheses
are precisely what the splitting classification must supply. -/
theorem gaussianIdealTailMass_le {ι : Type*}
    (S : Finset ι) (base : ι → Nat.Primes) (degreeOne : ι → Prop)
    [DecidablePred degreeOne]
    [DecidablePred (fun P : (Sᶜ : Set ι) => degreeOne P.val)]
    (B : ℝ) (hB : 2 ≤ B)
    (habove : ∀ P : (Sᶜ : Set ι), degreeOne P → B < (base P : ℝ))
    (hfiber1 : ∀ u : Finset (Sᶜ : Set ι), ∀ p : Nat.Primes,
      ((u.filter (fun P : (Sᶜ : Set ι) => degreeOne P.val)).filter
        fun P : (Sᶜ : Set ι) => base P.val = p).card ≤ 2)
    (hfiber2 : ∀ u : Finset (Sᶜ : Set ι), ∀ p : Nat.Primes,
      ((u.filter (fun P : (Sᶜ : Set ι) => ¬ degreeOne P.val)).filter
        fun P : (Sᶜ : Set ι) => base P.val = p).card ≤ 1) :
    (∑' P : (Sᶜ : Set ι),
      eulerMassTerm (gaussianIdealNorm base degreeOne) B P) ≤
        2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
          reciprocalSquareConstant := by
  classical
  apply Real.tsum_le_of_sum_le (fun P => by
    unfold eulerMassTerm
    have hpp : 0 < (base P : ℝ) := by
      exact_mod_cast (base P).property.pos
    have hp : 0 < gaussianIdealNorm base degreeOne P := by
      dsimp [gaussianIdealNorm]
      split_ifs <;> positivity
    exact mul_nonneg (one_div_nonneg.mpr hp.le) (Real.exp_nonneg _))
  intro u
  let base' : (Sᶜ : Set ι) → Nat.Primes := fun P => base P
  let degreeOne' : (Sᶜ : Set ι) → Prop := fun P => degreeOne P
  have hfinite := gaussianFiniteSmoothedTail_le u base' degreeOne'
    B hB
    (by intro P hP hd; exact habove P hd)
    (by intro p; exact hfiber1 u p)
    (by intro p; exact hfiber2 u p)
  have hnorm (P : (Sᶜ : Set ι)) :
      gaussianIdealNorm base' degreeOne' P =
        gaussianIdealNorm base degreeOne P.val := by
    by_cases hd : degreeOne P.val
    · simp [gaussianIdealNorm, base', degreeOne', hd]
    · simp [gaussianIdealNorm, base', degreeOne', hd]
  have hsum :
      (∑ P ∈ u, eulerMassTerm (gaussianIdealNorm base' degreeOne') B P) =
        ∑ P ∈ u, eulerMassTerm (gaussianIdealNorm base degreeOne) B P := by
    apply Finset.sum_congr rfl
    intro P _
    simp only [eulerMassTerm]
    rw [hnorm P]
  rw [hsum] at hfinite
  exact hfinite

end Erdos940.Quartic
