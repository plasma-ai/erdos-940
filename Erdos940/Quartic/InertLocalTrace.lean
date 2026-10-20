import Erdos940.Quartic.QuadraticZeroCount
import Erdos940.Quartic.LocalQuartic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The local trace at primes congruent to three modulo four

At such primes, fourth-power fibers and square fibers have the same size.
The four-variable quadratic zero count therefore gives the exact quartic
zero count and identifies its normalized first-order trace with the Legendre
symbol of the coefficient product.
-/

namespace Erdos940.Quartic

variable {q : ℕ} [Fact q.Prime]

/-- The coefficient of `(q-1)/q²` in the normalized quartic zero count. -/
noncomputable def inertLocalTrace (q : ℕ) [Fact q.Prime]
    (a : Fin 4 → ZMod q) : ℚ :=
  ((localQuarticCount (ZMod q) 0 a : ℚ) - (q : ℚ) ^ 3) /
    (((q : ℚ) - 1) * (q : ℚ))

/-- The exact zero count underlying the inert-prime trace formula. -/
theorem inert_quartic_zero_count (hmod : q % 4 = 3)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) :
    (localQuarticCount (ZMod q) 0 a : ℤ) =
      (q : ℤ) ^ 3 + ((q : ℤ) - 1) * (q : ℤ) *
        quadraticChar (ZMod q) (∏ i, a i) := by
  have hodd : q ≠ 2 := by omega
  have hmod' : Fintype.card (ZMod q) % 4 = 3 := by
    simpa only [ZMod.card] using hmod
  rw [localQuarticCount_eq_quadraticCount_of_mod_four_three
    (ZMod q) 0 a hmod']
  simpa only [Nat.card_eq_fintype_card] using
    (zmod_quadratic_four_zero_count hodd a ha)

/-- Equation (11): at an inert prime the normalized quartic trace is the
quadratic character of the coefficient product. -/
theorem inertLocalTrace_eq_quadraticChar (hmod : q % 4 = 3)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) :
    inertLocalTrace q a = (quadraticChar (ZMod q) (∏ i, a i) : ℚ) := by
  classical
  have hcountQ :
      (localQuarticCount (ZMod q) 0 a : ℚ) =
        (q : ℚ) ^ 3 + ((q : ℚ) - 1) * (q : ℚ) *
          (quadraticChar (ZMod q) (∏ i, a i) : ℚ) := by
    exact_mod_cast inert_quartic_zero_count hmod a ha
  have hq : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hq1 : (q : ℚ) - 1 ≠ 0 := by
    have hqNat : 3 ≤ q := by
      have htwo := (Fact.out : q.Prime).two_le
      omega
    have hqRat : (3 : ℚ) ≤ q := by exact_mod_cast hqNat
    linarith
  unfold inertLocalTrace
  apply (div_eq_iff (mul_ne_zero hq1 hq)).2
  rw [hcountQ]
  ring

/-- The same trace in the classical Legendre-symbol notation.  The integer
`D` can be the product of any integer lifts of the four coefficients. -/
theorem inertLocalTrace_eq_legendre (hmod : q % 4 = 3)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) (D : ℤ)
    (hD : (D : ZMod q) = ∏ i, a i) :
    inertLocalTrace q a = (legendreSym q D : ℚ) := by
  rw [inertLocalTrace_eq_quadraticChar hmod a ha]
  change (quadraticChar (ZMod q) (∏ i, a i) : ℚ) =
    (quadraticChar (ZMod q) (D : ZMod q) : ℚ)
  rw [hD]

/-- Equations (10)–(11) together, written as the normalized local density. -/
theorem inertLocalDensity_eq_legendre (hmod : q % 4 = 3)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) (D : ℤ)
    (hD : (D : ZMod q) = ∏ i, a i) :
    (localQuarticCount (ZMod q) 0 a : ℚ) / (q : ℚ) ^ 3 =
      1 + ((q : ℚ) - 1) / (q : ℚ) ^ 2 * (legendreSym q D : ℚ) := by
  have hχ : quadraticChar (ZMod q) (∏ i, a i) = legendreSym q D := by
    change quadraticChar (ZMod q) (∏ i, a i) =
      quadraticChar (ZMod q) (D : ZMod q)
    rw [hD]
  have hc := inert_quartic_zero_count hmod a ha
  rw [hχ] at hc
  have hcQ :
      (localQuarticCount (ZMod q) 0 a : ℚ) =
        (q : ℚ) ^ 3 + ((q : ℚ) - 1) * (q : ℚ) *
          (legendreSym q D : ℚ) := by
    exact_mod_cast hc
  have hq : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [hcQ]
  field_simp [hq]

end Erdos940.Quartic
