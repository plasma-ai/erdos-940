import Erdos940.Quartic.RationalEulerTail
import Erdos940.Quartic.GaussianIdealEulerProduct
import Erdos940.Quartic.EulerProductInequality
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Euler logarithm of a rational Dirichlet constituent

The Dirichlet L-series Euler product identifies the prime logarithm;
the first powers dominate its real part up to an absolutely summable
reciprocal-square error.
-/

namespace Erdos940.Quartic

open Finset


noncomputable def rationalDirichletPrimeTerm {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (P : Nat.Primes) : ℂ :=
  (rationalPrimeMass B P : ℂ) * χ (P : ℕ)

theorem rationalPrimeMass_eq_inv_cpow (B : ℝ) (P : Nat.Primes) :
    (rationalPrimeMass B P : ℂ) =
      (P : ℂ) ^ (-(1 + 1 / Real.log B : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < P := by exact_mod_cast P.property.pos
  have hmass := eulerSmoothedTerm_eq_power
    (fun Q : Nat.Primes => (Q : ℝ)) (fun _ => (1 : ℝ)) B P hp
  have hreal : rationalPrimeMass B P =
      (P : ℝ) ^ (-(1 + 1 / Real.log B : ℝ)) := by
    rw [Real.rpow_neg hp.le]
    simpa [rationalPrimeMass, eulerMassTerm, eulerSmoothedTerm] using hmass
  rw [hreal, Complex.ofReal_cpow hp.le]
  push_cast
  rfl

theorem rationalDirichletPrimeTerm_eq_euler {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (P : Nat.Primes) :
    rationalDirichletPrimeTerm χ B P =
      χ P * (P : ℂ) ^ (-(1 + 1 / Real.log B : ℝ) : ℂ) := by
  rw [rationalDirichletPrimeTerm, rationalPrimeMass_eq_inv_cpow]
  ring

theorem rationalDirichletPrimeTerm_re {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (P : Nat.Primes) :
    (rationalDirichletPrimeTerm χ B P).re =
      eulerSmoothedTerm (fun Q : Nat.Primes => (Q : ℝ))
        (fun Q => (χ (Q : ℕ)).re) B P := by
  simp only [rationalDirichletPrimeTerm, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  simp only [rationalPrimeMass, eulerMassTerm, eulerSmoothedTerm]
  ring

theorem rationalDirichletPrimeTerm_norm_le_mass {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (P : Nat.Primes) :
    ‖rationalDirichletPrimeTerm χ B P‖ ≤ rationalPrimeMass B P := by
  have hmass : 0 ≤ rationalPrimeMass B P := by
    unfold rationalPrimeMass eulerMassTerm
    positivity
  rw [rationalDirichletPrimeTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmass]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (χ.norm_le_one (P : ℕ)) hmass

theorem rationalDirichletPrimeTerm_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (hB : 1 < B) :
    Summable (rationalDirichletPrimeTerm χ B) := by
  apply (rationalPrimeMass_summable B hB).of_norm_bounded
  exact rationalDirichletPrimeTerm_norm_le_mass χ B

theorem rationalDirichletPrimeTerm_norm_le_inv (q : ℕ)
    (χ : DirichletCharacter ℂ q) (B : ℝ) (hB : 1 < B)
    (P : Nat.Primes) :
    ‖rationalDirichletPrimeTerm χ B P‖ ≤ 1 / (P : ℝ) := by
  have hp : (0 : ℝ) < P := by exact_mod_cast P.property.pos
  have hp1 : (1 : ℝ) ≤ P := by exact_mod_cast P.property.one_le
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg hp1
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hexp : Real.exp (-(Real.log (P : ℝ) / Real.log B)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact neg_nonpos.mpr (div_nonneg hlogP hlogB.le)
  have hmass : rationalPrimeMass B P ≤ 1 / (P : ℝ) := by
    dsimp [rationalPrimeMass, eulerMassTerm]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 1 / (P : ℝ))
  exact (rationalDirichletPrimeTerm_norm_le_mass χ B P).trans hmass

/-- The second and higher prime powers cost at most a fixed square-sum
constant, independently of the Dirichlet modulus and cutoff. -/
theorem rationalDirichletPrimeTerm_square_sum_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (hB : 1 < B) :
    Summable (fun P : Nat.Primes => ‖rationalDirichletPrimeTerm χ B P‖ ^ 2) ∧
    (∑' P : Nat.Primes, ‖rationalDirichletPrimeTerm χ B P‖ ^ 2) ≤
      reciprocalSquareConstant := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hprime : Summable (fun P : Nat.Primes => (1 : ℝ) / (P : ℝ) ^ 2) :=
    hbase.comp_injective Nat.Primes.coe_nat_injective
  have hpoint (P : Nat.Primes) :
      ‖rationalDirichletPrimeTerm χ B P‖ ^ 2 ≤
        (1 : ℝ) / (P : ℝ) ^ 2 := by
    have hp : (0 : ℝ) < P := by exact_mod_cast P.property.pos
    have h := rationalDirichletPrimeTerm_norm_le_inv q χ B hB P
    have hsq : ‖rationalDirichletPrimeTerm χ B P‖ ^ 2 ≤
        (1 / (P : ℝ)) ^ 2 := by gcongr
    simpa only [one_div, inv_pow] using hsq
  have hsum : Summable
      (fun P : Nat.Primes => ‖rationalDirichletPrimeTerm χ B P‖ ^ 2) :=
    hprime.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' P : Nat.Primes, (1 : ℝ) / (P : ℝ) ^ 2 :=
      hsum.tsum_le_tsum hpoint hprime
    _ ≤ reciprocalSquareConstant := by
      unfold reciprocalSquareConstant
      exact hprime.tsum_le_tsum_of_inj (fun P : Nat.Primes => (P : ℕ))
        Nat.Primes.coe_nat_injective
        (fun _ _ => by positivity) (fun _ => le_rfl) hbase

/-- The rational Dirichlet Euler product gives the required first-prime
logarithm bound with an absolute reciprocal-square error. -/
theorem rationalDirichletEulerLog_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (B : ℝ) (hB : 1 < B) :
    (∑' P : Nat.Primes,
      eulerSmoothedTerm (fun Q : Nat.Primes => (Q : ℝ))
        (fun Q => (χ (Q : ℕ)).re) B P) ≤
      Real.log ‖LSeries (fun n : ℕ => χ (n : ZMod q))
        ((1 + 1 / Real.log B : ℝ) : ℂ)‖ +
        reciprocalSquareConstant / 2 := by
  let σ : ℝ := 1 + 1 / Real.log B
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have hσ : 1 < σ := by
    dsimp [σ]
    have hrecip : 0 < 1 / Real.log B := by positivity
    linarith
  have hne (P : Nat.Primes) : rationalDirichletPrimeTerm χ B P ≠ 1 := by
    intro hz
    have hp : (1 : ℝ) < P := by exact_mod_cast P.property.one_lt
    have hinv : 1 / (P : ℝ) < 1 := by
      exact (div_lt_iff₀ (by linarith : (0 : ℝ) < P)).2 (by simpa using hp)
    have hle := rationalDirichletPrimeTerm_norm_le_inv q χ B hB P
    rw [hz, norm_one] at hle
    linarith
  have hseries := rationalDirichletPrimeTerm_summable χ B hB
  obtain ⟨hsq, hsqBound⟩ := rationalDirichletPrimeTerm_square_sum_le χ B hB
  have hEuler : Complex.exp
      (∑' P : Nat.Primes,
        -Complex.log (1 - rationalDirichletPrimeTerm χ B P)) =
      LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ) := by
    simpa only [rationalDirichletPrimeTerm_eq_euler, σ] using
      (DirichletCharacter.LSeries_eulerProduct_exp_log χ
        (by simpa only [Complex.ofReal_re] using hσ :
          1 < (σ : ℂ).re))
  have h := GaussianIdealEulerProduct.re_tsum_le_log_norm_of_exp_euler_log
    (rationalDirichletPrimeTerm χ B)
    (LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ))
    hne hseries hsq hEuler
  simp only [rationalDirichletPrimeTerm_re] at h
  exact h.trans (by gcongr)

end Erdos940.Quartic
