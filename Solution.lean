import Erdos940.FinalAssembly

/-!
# Proof of the cubic and quartic cases of Erdős Problem 940

Comparator checks the four theorems in this module against the Mathlib-only
statements in `Challenge.lean`.
-/

open Filter

namespace Erdos940

/-- The integers that are not a sum of at most three cube-full numbers have
positive lower density. -/
theorem cubic_complement_density :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable 3 n}.ncard :=
  cubic_complement_density_proved

/-- The integers that are not a sum of at most four 4-full numbers have
positive lower density. -/
theorem quartic_complement_density :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable 4 n}.ncard :=
  quartic_complement_density_proved

/-- Infinitely many integers are not a sum of at most three cube-full
numbers. -/
theorem cubic_large_integers :
    ¬ (∀ᶠ x in atTop, ∃ (S : Multiset ℕ), S.card ≤ 3 ∧ (∀ s ∈ S, (3).Full s) ∧ x = S.sum) :=
  cubic_large_integers_proved

/-- Infinitely many integers are not a sum of at most four 4-full numbers. -/
theorem quartic_large_integers :
    ¬ (∀ᶠ x in atTop, ∃ (S : Multiset ℕ), S.card ≤ 4 ∧ (∀ s ∈ S, (4).Full s) ∧ x = S.sum) :=
  quartic_large_integers_proved

end Erdos940
