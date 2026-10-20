import Erdos940.Quartic.GaussianIdealLatticeSeries
import Erdos940.Quartic.GaussianZeroMean

/-!
# Logarithmic bound for the quartic ideal-character L-series

The conductor period, residue mean-zero argument, analytic Gaussian lattice
estimate, and four-generators identity combine here. The only arithmetic
input is a residue-unit multiplier on which the quartic character is
nontrivial.
-/

namespace Erdos940.Quartic.GaussianIdealLBound

open scoped NumberField
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianZeroMean

/-- The independent ideal-weight definitions in the unit-orbit and
mean-zero modules are the same zero-extended character. -/
theorem quarticIdealWeight_eq_zeroMean
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I : Ideal (𝓞 GaussianField)) :
    GaussianIdealLatticeSeries.quarticIdealWeight R ι I =
      GaussianZeroMean.quarticIdealWeight R ι I := by
  rfl

theorem quarticIdealCoeff_weight_mul
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I J : Ideal (𝓞 GaussianField)) :
    GaussianIdealLatticeSeries.quarticIdealWeight R ι (I * J) =
      GaussianIdealLatticeSeries.quarticIdealWeight R ι I *
        GaussianIdealLatticeSeries.quarticIdealWeight R ι J := by
  rw [quarticIdealWeight_eq_zeroMean,
    GaussianZeroMean.quarticIdealWeight_mul]
  rw [quarticIdealWeight_eq_zeroMean, quarticIdealWeight_eq_zeroMean]

/-- The norm-indexed ideal L-series attached to a nonzero odd rational
radicand has logarithmic size, conditional only on an explicit nontrivial
residue-unit multiplier. -/
theorem norm_quarticIdealLSeries_le_log_of_signed_multiplier
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (quarticIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖ ≤
      (162 * Real.log (((64 * R.natAbs : ℕ) : ℝ) ^ 2) + 648) / 4 := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  exact norm_quarticIdealLSeries_le_log (64 * R.natAbs)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_signed_odd_periodic R hR0 hRodd ι)
    (quarticIdealLatticeWeight_signed_residue_mean_zero_of_multiplier
      R hR0 hRodd ι a ha hunit) σ hσ₁ hσ₂

end Erdos940.Quartic.GaussianIdealLBound
