import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential parameter choice

A summable family of nonnegative weights remains summable after multiplication by
exponential damping. If every rate is positive, the damped sum tends to zero,
even when the rates have no uniform positive lower bound.
-/

namespace Erdos940.Quartic

open Filter
open scoped Topology

variable {ι : Type*} (w c : ι → ℝ)

/-- Dominated convergence for a summable family of exponentially damped weights. -/
theorem tendsto_tsum_weight_mul_exp_neg
    (hw : Summable w) (hw_nonneg : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 < c i) :
    Tendsto (fun T : ℕ => ∑' i, w i * Real.exp (-((T : ℝ) * c i)))
      atTop (𝓝 0) := by
  have hpoint (i : ι) :
      Tendsto (fun T : ℕ => w i * Real.exp (-((T : ℝ) * c i))) atTop (𝓝 0) := by
    have hrate : Tendsto (fun T : ℕ => (T : ℝ) * c i) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (hc i)
    have hexp : Tendsto (fun T : ℕ => Real.exp (-((T : ℝ) * c i))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hrate
    simpa using (tendsto_const_nhds.mul hexp :
      Tendsto (fun T : ℕ => w i * Real.exp (-((T : ℝ) * c i))) atTop (𝓝 (w i * 0)))
  have hbound :
      ∀ᶠ T : ℕ in atTop, ∀ i : ι,
        ‖w i * Real.exp (-((T : ℝ) * c i))‖ ≤ w i := by
    apply Eventually.of_forall
    intro T i
    have harg : -((T : ℝ) * c i) ≤ 0 := by
      exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hc i)))
    have hexp_le : Real.exp (-((T : ℝ) * c i)) ≤ 1 := by
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr harg)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_nonneg i) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (hw_nonneg i) hexp_le
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun T : ℕ => fun i : ι => w i * Real.exp (-((T : ℝ) * c i)))
    (g := fun _ : ι => (0 : ℝ)) (bound := w) hw hpoint hbound
  simpa using h

/-- Any positive target is eventually met by a finite natural-number parameter. -/
theorem exists_nat_forall_ge_tsum_weight_mul_exp_neg_lt
    (hw : Summable w) (hw_nonneg : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 < c i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T ≥ T₀,
      (∑' i, w i * Real.exp (-((T : ℝ) * c i))) < ε := by
  have hlim := tendsto_tsum_weight_mul_exp_neg w c hw hw_nonneg hc
  have hsmall : ∀ᶠ T : ℕ in atTop,
      (∑' i, w i * Real.exp (-((T : ℝ) * c i))) < ε :=
    hlim.eventually (eventually_lt_nhds hε)
  exact eventually_atTop.mp hsmall

end Erdos940.Quartic
