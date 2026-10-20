import Erdos940.Quartic.QuarticElevenBoundCombination
import Erdos940.Quartic.RationalConstituentEstimate
import Erdos940.Quartic.GaussianFinitePrimeSumBound
import Erdos940.Quartic.GaussianCMConstituentBridge

/-!
# The quartic case of Erdős Problem 940

The four-powerful complement has positive lower density, and therefore is
infinite. This is the infinitude assertion for `r = 4`, not the conjectural
density-zero assertion for the representable set.
-/

namespace Erdos940.Quartic

open GaussianFinitePrimeSumBound
open GaussianCMConstituentBridge

theorem positiveLowerDensity_four :
    HasPositiveLowerDensityComplementFor 4 := by
  let C₀ : ℝ :=
    Real.log 13 + Real.log (2 + 9 / Real.log 2) +
      Real.log 4 * (1 + 1 / Real.log 2) +
      Real.log 4 * (1 + 2 / Real.log 2) +
      reciprocalSquareConstant / 2
  let Cfinite : ℝ :=
    Real.log 13 + Real.log (162 + 648 / Real.log 2) +
      6 * Real.log 4 * (1 + 1 / Real.log 2) +
      (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant) + 2 * reciprocalSquareConstant
  let CCM : ℝ :=
    (Real.log 13 + Real.log (162 + 648 / Real.log 2) +
      6 * Real.log 4 * (1 + 1 / Real.log 2) +
      (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant) + reciprocalSquareConstant) +
      reciprocalSquareConstant
  apply positiveLowerDensity_four_of_three_prime_sum_bounds C₀ Cfinite CCM
  · intro B hB d hreg
    exact regular_baseConstituent_zero_quarticBasePrimes_le B hB d hreg
  · intro B hB d hreg j hj0 hj10
    have hv0 : j.val ≠ 0 := by
      intro h
      apply hj0
      exact Fin.ext h
    have hv10 : j.val ≠ 10 := by
      intro h
      apply hj10
      exact Fin.ext h
    have hj : 1 ≤ j.val ∧ j.val ≤ 9 := by
      have hlt := j.isLt
      omega
    exact regular_baseConstituent_finite_quarticBasePrimes_le
      B hB d hreg j hj
  · intro B hB d _
    simpa only [CCM, add_assoc] using
      baseConstituent_ten_good_sum_le_coefficient_loglog d B hB

end Erdos940.Quartic

namespace Erdos940

/-- The E940 r = 4 coinfinitude claim: infinitely many natural numbers are not
a sum of at most four 4-powerful numbers. -/
theorem coinfiniteFor_four : CoinfiniteFor 4 :=
  coinfiniteFor_of_positiveLowerDensity Quartic.positiveLowerDensity_four

end Erdos940
