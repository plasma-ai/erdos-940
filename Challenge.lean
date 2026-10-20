module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Erdős Problem 940: sums of r-powerful numbers

A natural number `n` is `r`-powerful (or `r`-full) if `p ^ r ∣ n` for every
prime `p ∣ n`. Call `n` representable for `r` if it is the sum of at most `r`
`r`-powerful natural numbers. Erdős asked, for `r ≥ 3`, whether infinitely
many integers are not representable, and whether the representable integers
have density zero.

**Claim.** For `r = 3` and `r = 4`, the integers that are not representable
have positive lower density: for some positive integer `C`, at least `N / C`
of the integers below `N` are not representable, for all large `N`. In
particular, infinitely many integers are not representable.

The case `r = 3` is due to Beyer de Ryke (arXiv:2609.35772). To our knowledge,
the case `r = 4` is new. Whether the representable integers have density zero
remains open for every `r ≥ 3`, and so does the infinitude question for every
`r ≥ 5`. Thomas F. Bloom catalogs the question as
[Erdős Problem 940](https://www.erdosproblems.com/940).

`Nat.Full` is copied verbatim from `formal-conjectures`
(`FormalConjecturesForMathlib/Data/Nat/Full.lean`), and the infinitude
statements are its `erdos_940.variants.large_integers` at `r = 3` and `r = 4`.
The numbers `0` and `1` are `r`-full, so a representation may use fewer than
`r` positive summands.

The four theorems below have deliberate proof holes. `Solution.lean` supplies
their proofs, and Comparator checks them against these statements.
-/

@[expose] public section

open Filter

namespace Nat

/--
A natural number $n$ is said to be $k$-full (or $k$-powerful) if for every prime factor $p$ of $n$,
the $k$-th power $p^k$ also divides $n$.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

end Nat

namespace Erdos940

/-- `n` is the sum of at most `r` `r`-powerful natural numbers. -/
def Representable (r : ℕ) (n : ℕ) : Prop :=
  ∃ S : Multiset ℕ,
    S.card ≤ r ∧ (∀ s ∈ S, Nat.Full r s) ∧ n = S.sum

/-- The integers that are not a sum of at most three cube-full numbers have
positive lower density. -/
theorem cubic_complement_density :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable 3 n}.ncard := by
  sorry

/-- The integers that are not a sum of at most four 4-full numbers have
positive lower density. -/
theorem quartic_complement_density :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ N in atTop,
      N ≤ C * {n : ℕ | n < N ∧ ¬ Representable 4 n}.ncard := by
  sorry

/-- Infinitely many integers are not a sum of at most three cube-full
numbers. -/
theorem cubic_large_integers :
    ¬ (∀ᶠ x in atTop, ∃ (S : Multiset ℕ), S.card ≤ 3 ∧ (∀ s ∈ S, (3).Full s) ∧ x = S.sum) := by
  sorry

/-- Infinitely many integers are not a sum of at most four 4-full numbers. -/
theorem quartic_large_integers :
    ¬ (∀ᶠ x in atTop, ∃ (S : Multiset ℕ), S.card ≤ 4 ∧ (∀ s ∈ S, (4).Full s) ∧ x = S.sum) := by
  sorry

end Erdos940
