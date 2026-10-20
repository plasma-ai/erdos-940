import Erdos940.Quartic.GlobalElevenCharacter
import Erdos940.Quartic.QuarticAnalyticConclusion

/-!
# The remaining prime-sum estimates

The complete local sieve, finite-field trace formula, and eleven-term
decomposition reduce the quartic theorem to a uniform upper bound for
each of the eleven explicit character prime sums.
-/

namespace Erdos940.Quartic

theorem positiveLowerDensity_four_of_eleven_prime_sum_bound
    (error : ℝ)
    (hSum : ∀ B, 3 ≤ B → ∀ d, ¬ExceptionalTuple d →
      ∀ j : Fin 11,
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + error) :
    HasPositiveLowerDensityComplementFor 4 :=
  positiveLowerDensity_four_of_eleven_character_estimates
    baseConstituent error baseConstituent_exact_on_base_primes hSum

end Erdos940.Quartic
