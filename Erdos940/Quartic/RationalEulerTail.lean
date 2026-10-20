import Erdos940.Quartic.EulerPrimeChebyshev

/-!
# Rational prime Euler logarithm and tail

This module supplies the analytic hypotheses of the finite-prime bound for
a rational Dirichlet character. The cutoff-dependent prime series is
absolutely convergent, its tail is controlled by the rational Chebyshev
estimate, and the Euler logarithm comes from Mathlib's Dirichlet L-series
Euler product.
-/

namespace Erdos940.Quartic

open Finset

noncomputable def rationalPrimeMass (B : ℝ) (P : Nat.Primes) : ℝ :=
  eulerMassTerm (fun Q : Nat.Primes => (Q : ℝ)) B P

/-- The rational prime mass is summable at the smoothed cutoff exponent. -/
theorem rationalPrimeMass_summable (B : ℝ) (hB : 1 < B) :
    Summable (rationalPrimeMass B) := by
  let σ : ℝ := 1 + 1 / Real.log B
  have hlog : 0 < Real.log B := Real.log_pos hB
  have hσ : 1 < σ := by
    dsimp [σ]
    have hrecip : 0 < 1 / Real.log B := by positivity
    linarith
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ σ) :=
    Real.summable_one_div_nat_rpow.mpr hσ
  have hprime : Summable (fun P : Nat.Primes => 1 / (P : ℝ) ^ σ) :=
    hbase.comp_injective Nat.Primes.coe_nat_injective
  convert hprime using 1
  funext P
  have hp : (0 : ℝ) < P := by exact_mod_cast P.property.pos
  simpa [rationalPrimeMass, eulerMassTerm, eulerSmoothedTerm, σ] using
    (eulerSmoothedTerm_eq_power (fun Q : Nat.Primes => (Q : ℝ))
      (fun _ => (1 : ℝ)) B P hp)

/-- The signed smoothed rational-prime series is summable, uniformly for
coefficients of modulus at most one. -/
theorem rationalSmoothedPrime_summable
    (c : Nat.Primes → ℝ) (B : ℝ) (hB : 1 < B)
    (hc : ∀ P, |c P| ≤ 1) :
    Summable (eulerSmoothedTerm (fun P : Nat.Primes => (P : ℝ)) c B) := by
  apply (rationalPrimeMass_summable B hB).of_norm_bounded
  intro P
  have hp : (0 : ℝ) < P := by exact_mod_cast P.property.pos
  have hmass : 0 ≤ rationalPrimeMass B P := by
    unfold rationalPrimeMass eulerMassTerm
    positivity
  change ‖c P / (P : ℝ) *
    Real.exp (-(Real.log (P : ℝ) / Real.log B))‖ ≤ rationalPrimeMass B P
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hp,
    abs_of_pos (Real.exp_pos _)]
  dsimp [rationalPrimeMass, eulerMassTerm]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hc P) hp.le) (Real.exp_pos _).le

/-- The rational prime tail satisfies the lower bound used in the finite
prime comparison. -/
theorem rationalSmoothedPrime_tail_lower
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hS : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ))
    (c : Nat.Primes → ℝ) (hc : ∀ P, |c P| ≤ 1) :
    -(Real.log 4 * (1 + 2 / Real.log 2)) ≤
      ∑' P : (Sᶜ : Set Nat.Primes),
        eulerSmoothedTerm (fun Q : Nat.Primes => (Q : ℝ)) c B P.val := by
  have hB' : 1 < B := by linarith
  have hmass : Summable
      (fun P : (Sᶜ : Set Nat.Primes) =>
        eulerMassTerm (fun Q : Nat.Primes => (Q : ℝ)) B P.val) :=
    (rationalPrimeMass_summable B hB').subtype _
  exact eulerTail_lower_of_mass S (fun P : Nat.Primes => (P : ℝ)) c B
    (Real.log 4 * (1 + 2 / Real.log 2))
    (fun P => by exact_mod_cast P.val.property.pos)
    (fun P => hc P)
    (rationalSmoothedPrime_summable c B hB' hc)
    hmass (rationalPrimeTailMass_le B hB S hS)

end Erdos940.Quartic
