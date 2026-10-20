import Erdos940.Cubic.Assembly
import Erdos940.Quartic.Result

/-!
# The cubic and quartic cases of Erdős Problem 940

The positive lower density bounds of `Erdos940.Cubic` and `Erdos940.Quartic`
count the nonrepresentable numbers below `N` with a filtered `Finset`. This
module restates them with `Set.ncard`, and restates the infinitude of the
nonrepresentable numbers as the failure of eventual representability.
-/

set_option autoImplicit false

namespace Erdos940

/-- The `Finset` count of nonrepresentable numbers below `N` agrees with the
cardinality of the corresponding set. -/
theorem ncard_eq_missingCount (r N : ℕ) :
    {n : ℕ | n < N ∧ ¬ Representable r n}.ncard = missingCount r N := by
  classical
  rw [missingCount, ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp

/-- Positive lower density of the complement, counted with `Set.ncard`. -/
theorem complement_density_of_positiveLowerDensity {r : ℕ}
    (h : HasPositiveLowerDensityComplementFor r) :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable r n}.ncard := by
  simp only [ncard_eq_missingCount]
  exact h

/-- A coinfinite representable set is not eventually everything. -/
theorem not_eventually_representable_of_coinfinite {r : ℕ}
    (h : CoinfiniteFor r) :
    ¬ (∀ᶠ x in Filter.atTop, Representable r x) := by
  intro hEventually
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hEventually
  exact h ((Set.finite_lt_nat a).subset fun n hn =>
    lt_of_not_ge fun hle => hn (ha n hle))

/-- The integers that are not a sum of at most three cube-full numbers have
positive lower density. -/
theorem cubic_complement_density_proved :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable 3 n}.ncard :=
  complement_density_of_positiveLowerDensity positiveLowerDensityComplement_three

/-- The integers that are not a sum of at most four 4-full numbers have
positive lower density. -/
theorem quartic_complement_density_proved :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable 4 n}.ncard :=
  complement_density_of_positiveLowerDensity Quartic.positiveLowerDensity_four

/-- Infinitely many integers are not a sum of at most three cube-full
numbers. -/
theorem cubic_large_integers_proved :
    ¬ (∀ᶠ x in Filter.atTop, Representable 3 x) :=
  not_eventually_representable_of_coinfinite coinfiniteFor_three

/-- Infinitely many integers are not a sum of at most four 4-full numbers. -/
theorem quartic_large_integers_proved :
    ¬ (∀ᶠ x in Filter.atTop, Representable 4 x) :=
  not_eventually_representable_of_coinfinite coinfiniteFor_four

end Erdos940
