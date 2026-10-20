import Erdos940.Quartic.QuarticPrimeSumConclusion

/-!
# Combining the three classes of quartic character bounds

The eleven trace constituents divide into a rational quadratic term,
nine finite Gaussian terms, and a single CM term. The estimates for
these classes can use different uniform additive constants.
-/

namespace Erdos940.Quartic

theorem positiveLowerDensity_four_of_three_prime_sum_bounds
    (C₀ Cfinite CCM : ℝ)
    (hzero : ∀ B, 3 ≤ B → ∀ d, ¬ ExceptionalTuple d →
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d 0 p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + C₀)
    (hfinite : ∀ B, 3 ≤ B → ∀ d, ¬ ExceptionalTuple d →
      ∀ j : Fin 11, j ≠ 0 → j ≠ 10 →
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + Cfinite)
    (hCM : ∀ B, 3 ≤ B → ∀ d, ¬ ExceptionalTuple d →
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d 10 p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + CCM) :
    HasPositiveLowerDensityComplementFor 4 := by
  let error := max C₀ (max Cfinite CCM)
  apply positiveLowerDensity_four_of_eleven_prime_sum_bound error
  intro B hB d hreg j
  by_cases hj0 : j = 0
  · subst j
    exact (hzero B hB d hreg).trans (add_le_add_right (le_max_left _ _) _)
  by_cases hj10 : j = 10
  · subst j
    exact (hCM B hB d hreg).trans
      (add_le_add_right ((le_max_right _ _).trans (le_max_right _ _)) _)
  exact (hfinite B hB d hreg j hj0 hj10).trans
    (add_le_add_right ((le_max_left _ _).trans (le_max_right _ _)) _)

end Erdos940.Quartic
