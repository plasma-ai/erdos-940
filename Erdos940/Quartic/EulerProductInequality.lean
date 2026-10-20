import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Elementary quartic Euler-product majorization

The local trace expansion has the form
`ρ_p = 1 + (p-1)/p² * A_p`, with `|A_p| ≤ 21`. This file converts that
expansion to a product bound involving `∑ A_p/p`. No logarithm of a local
factor is taken, so zero factors are permitted.
-/

namespace Erdos940.Quartic

open Finset

/-- The abstract local factor appearing in the quartic trace expansion. -/
noncomputable def quarticEulerFactor (p : ℕ) (A : ℝ) : ℝ :=
  1 + ((p : ℝ) - 1) / (p : ℝ) ^ 2 * A

/-- A single factor is at most the exponential of its first-order trace
plus the quadratic-denominator error. No positivity of the factor is needed
for this one-factor inequality. -/
theorem quarticEulerFactor_le_exp (p : ℕ) (hp : 0 < p)
    (A : ℝ) (hA : |A| ≤ 21) :
    quarticEulerFactor p A ≤
      Real.exp (A / (p : ℝ) + 21 / (p : ℝ) ^ 2) := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hpNe : (p : ℝ) ≠ 0 := hpReal.ne'
  have hneg : -A ≤ 21 := by
    have := (abs_le.mp hA).1
    linarith
  have hu : ((p : ℝ) - 1) / (p : ℝ) ^ 2 * A ≤
      A / (p : ℝ) + 21 / (p : ℝ) ^ 2 := by
    have hident : ((p : ℝ) - 1) / (p : ℝ) ^ 2 * A =
        A / (p : ℝ) + (-A) / (p : ℝ) ^ 2 := by
      field_simp
      ring
    rw [hident]
    have hdiv : (-A) / (p : ℝ) ^ 2 ≤ 21 / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hneg (sq_nonneg _)
    linarith
  calc
    quarticEulerFactor p A ≤
        Real.exp (((p : ℝ) - 1) / (p : ℝ) ^ 2 * A) := by
      unfold quarticEulerFactor
      simpa only [add_comm] using
        Real.add_one_le_exp (((p : ℝ) - 1) / (p : ℝ) ^ 2 * A)
    _ ≤ Real.exp (A / (p : ℝ) + 21 / (p : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr hu

/-- The finite Euler product is controlled by the trace prime sum and an
absolutely summable square-reciprocal error. Factors may be zero. -/
theorem quarticEulerProduct_le_exp (Q : Finset ℕ) (A : ℕ → ℝ)
    (hpos : ∀ p ∈ Q, 0 < p)
    (hA : ∀ p ∈ Q, |A p| ≤ 21)
    (hfactor : ∀ p ∈ Q, 0 ≤ quarticEulerFactor p (A p)) :
    (∏ p ∈ Q, quarticEulerFactor p (A p)) ≤
      Real.exp ((∑ p ∈ Q, A p / (p : ℝ)) +
        21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) := by
  calc
    (∏ p ∈ Q, quarticEulerFactor p (A p)) ≤
        ∏ p ∈ Q, Real.exp (A p / (p : ℝ) + 21 / (p : ℝ) ^ 2) :=
      Finset.prod_le_prod₀ (fun p hp => hfactor p hp)
        (fun p hp => quarticEulerFactor_le_exp p (hpos p hp) (A p) (hA p hp))
    _ = Real.exp (∑ p ∈ Q,
          (A p / (p : ℝ) + 21 / (p : ℝ) ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp ((∑ p ∈ Q, A p / (p : ℝ)) +
          21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) := by
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- A fixed absolute constant bounding every finite sum of reciprocal
squares. Its exact numerical value is immaterial to the sieve. -/
noncomputable def reciprocalSquareConstant : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2

theorem finite_reciprocalSquares_le (Q : Finset ℕ) :
    (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ reciprocalSquareConstant := by
  unfold reciprocalSquareConstant
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).sum_le_tsum
    Q (fun _ _ => by positivity)

/-- The same Euler-product bound with a constant independent of the chosen
finite prime set. -/
theorem quarticEulerProduct_le_exp_uniform (Q : Finset ℕ) (A : ℕ → ℝ)
    (hpos : ∀ p ∈ Q, 0 < p)
    (hA : ∀ p ∈ Q, |A p| ≤ 21)
    (hfactor : ∀ p ∈ Q, 0 ≤ quarticEulerFactor p (A p)) :
    (∏ p ∈ Q, quarticEulerFactor p (A p)) ≤
      Real.exp ((∑ p ∈ Q, A p / (p : ℝ)) +
        21 * reciprocalSquareConstant) := by
  calc
    (∏ p ∈ Q, quarticEulerFactor p (A p)) ≤
        Real.exp ((∑ p ∈ Q, A p / (p : ℝ)) +
          21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) :=
      quarticEulerProduct_le_exp Q A hpos hA hfactor
    _ ≤ Real.exp ((∑ p ∈ Q, A p / (p : ℝ)) +
          21 * reciprocalSquareConstant) := by
      apply Real.exp_le_exp.mpr
      gcongr
      exact finite_reciprocalSquares_le Q

end Erdos940.Quartic
