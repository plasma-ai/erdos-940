import Erdos940.Quartic.LocalQuadraticPerturbation
import Mathlib.NumberTheory.Padics.WithVal

/-!
# Congruence targets and local quadratic perturbation

Integer targets divisible by the local prime (or by eight at the dyadic
place) become small after division by an integer unit term.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

local instance finitePlacePadicPrimeFactForCongruence
    (place : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (finitePlacePadicPrime place : ℕ)) :=
  ⟨(finitePlacePadicPrime place).2⟩

/-- An integer prime to `p` has an integral inverse in `ℚ_p`. -/
theorem padic_natCast_inverse_integral
    (p U : ℕ) [Fact p.Prime] (hU : ¬p ∣ U) :
    ∃ u : ℤ_[p], ((U : ℚ_[p])⁻¹) = (u : ℚ_[p]) := by
  have hunit : ‖(U : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hU)
  refine ⟨(U : ℤ_[p]).inv, ?_⟩
  have hmul : (U : ℚ_[p]) * (((U : ℤ_[p]).inv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun z : ℤ_[p] => (z : ℚ_[p]))
      (PadicInt.mul_inv hunit)
  exact inv_eq_of_mul_eq_one_right hmul

/-- Dividing a multiple of `m` by an integer `p`-adic unit preserves
membership in `mℤ_p`. -/
theorem padic_nat_div_unit_is_multiple
    (p m N U : ℕ) [Fact p.Prime] (hN : m ∣ N) (hU : ¬p ∣ U) :
    ∃ y : ℤ_[p], (N : ℚ_[p]) / (U : ℚ_[p]) =
      (m : ℚ_[p]) * (y : ℚ_[p]) := by
  obtain ⟨k, rfl⟩ := hN
  obtain ⟨u, hu⟩ := padic_natCast_inverse_integral p U hU
  refine ⟨(k : ℤ_[p]) * u, ?_⟩
  rw [div_eq_mul_inv, hu]
  push_cast
  ring

/-- At an odd finite place, a `p`-divisible integer value divided by an
integer unit term satisfies the square-root smallness criterion. -/
theorem finiteCompletion_small_of_odd_nat_dvd_unit
    (place : HeightOneSpectrum (𝓞 ℚ)) (N U : ℕ)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hN : (finitePlacePadicPrime place : ℕ) ∣ N)
    (hU : ¬(finitePlacePadicPrime place : ℕ) ∣ U) :
    finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (U : place.adicCompletion ℚ)) := by
  classical
  let p := finitePlacePadicPrime place
  obtain ⟨y, hy⟩ := padic_nat_div_unit_is_multiple p.1 p.1 N U hN hU
  left
  refine ⟨hodd, y, ?_⟩
  simpa using hy

/-- Rational terms can be used in the odd-prime perturbation whenever their
inverse is integral in the corresponding `p`-adic field. -/
theorem finiteCompletion_small_of_odd_nat_dvd_rational_unit
    (place : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ) (U : ℚ)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hN : (finitePlacePadicPrime place : ℕ) ∣ N)
    (hU : ∃ u : ℤ_[finitePlacePadicPrime place],
      finitePlacePadicEquiv place
          ((U : place.adicCompletion ℚ)⁻¹) =
        (u : ℚ_[finitePlacePadicPrime place])) :
    finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (U : place.adicCompletion ℚ)) := by
  classical
  let p := finitePlacePadicPrime place
  obtain ⟨k, hk⟩ := hN
  obtain ⟨u, hu⟩ := hU
  subst N
  left
  refine ⟨hodd, (k : ℤ_[p]) * u, ?_⟩
  rw [div_eq_mul_inv, map_mul, hu]
  simp only [Nat.cast_mul, map_mul, map_natCast, PadicInt.coe_mul,
    PadicInt.coe_natCast]
  ring

/-- A rational number whose reduced numerator is prime to `p` has a
`p`-adically integral inverse. The denominator need not be a unit. -/
theorem finiteCompletion_rational_inverse_integral_of_num_not_dvd
    (place : HeightOneSpectrum (𝓞 ℚ)) (U : ℚ)
    (hU : ¬(finitePlacePadicPrime place : ℕ) ∣ U.num.natAbs) :
    ∃ u : ℤ_[finitePlacePadicPrime place],
      finitePlacePadicEquiv place ((U : place.adicCompletion ℚ)⁻¹) =
        (u : ℚ_[finitePlacePadicPrime place]) := by
  classical
  let p := finitePlacePadicPrime place
  have hU0 : U ≠ 0 := by
    intro h
    apply hU
    simp [h]
  have hden : ¬ p.1 ∣ (U⁻¹).den := by
    simpa [Rat.den_inv_of_ne_zero hU0] using hU
  have hnorm : ‖((U⁻¹ : ℚ) : ℚ_[p])‖ ≤ 1 :=
    (Padic.norm_rat_le_one_iff_padicValuation_le_one p.1).mpr
      (Rat.padicValuation_le_one_iff.mpr hden)
  refine ⟨⟨((U⁻¹ : ℚ) : ℚ_[p]), hnorm⟩, ?_⟩
  simp

/-- Arithmetic criterion for the rational-unit version: it is enough that
the reduced numerator of the rational quadratic term be prime to `p`. -/
theorem finiteCompletion_small_of_odd_nat_dvd_rational_num_unit
    (place : HeightOneSpectrum (𝓞 ℚ)) (N : ℕ) (U : ℚ)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hN : (finitePlacePadicPrime place : ℕ) ∣ N)
    (hU : ¬(finitePlacePadicPrime place : ℕ) ∣ U.num.natAbs) :
    finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (U : place.adicCompletion ℚ)) :=
  finiteCompletion_small_of_odd_nat_dvd_rational_unit place N U hodd hN
    (finiteCompletion_rational_inverse_integral_of_num_not_dvd place U hU)

/-- At the dyadic finite place, an eight-divisible integer value divided
by an odd integer term satisfies the square-root smallness criterion. -/
theorem finiteCompletion_small_of_dyadic_nat_dvd_unit
    (place : HeightOneSpectrum (𝓞 ℚ)) (N U : ℕ)
    (hdyadic : (finitePlacePadicPrime place : ℕ) = 2)
    (hN : 8 ∣ N) (hU : ¬(finitePlacePadicPrime place : ℕ) ∣ U) :
    finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (U : place.adicCompletion ℚ)) := by
  classical
  let p := finitePlacePadicPrime place
  obtain ⟨y, hy⟩ := padic_nat_div_unit_is_multiple p.1 8 N U hN hU
  right
  refine ⟨hdyadic, y, ?_⟩
  simpa using hy

/-- The exact target `N ≡ p (mod p²)` supplies the divisibility needed by
the odd-prime perturbation lemma. -/
theorem finiteCompletion_small_of_odd_prime_square_target
    (place : HeightOneSpectrum (𝓞 ℚ)) (N U : ℕ)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hN : N % (finitePlacePadicPrime place : ℕ) ^ 2 =
      (finitePlacePadicPrime place : ℕ))
    (hU : ¬(finitePlacePadicPrime place : ℕ) ∣ U) :
    finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (U : place.adicCompletion ℚ)) := by
  let p : ℕ := finitePlacePadicPrime place
  have hpp : p ∣ p ^ 2 := by
    use p
    ring
  have hmod : N % p = 0 := by
    calc
      N % p = (N % (p ^ 2)) % p := (Nat.mod_mod_of_dvd N hpp).symm
      _ = p % p := congrArg (fun k : ℕ => k % p) hN
      _ = 0 := Nat.mod_self p
  exact finiteCompletion_small_of_odd_nat_dvd_unit place N U hodd
    (Nat.dvd_of_mod_eq_zero hmod) hU

/-- The exact target `N ≡ 8 (mod 16)` supplies eight-divisibility for
the dyadic perturbation lemma. -/
theorem finiteCompletion_small_of_dyadic_sixteen_target
    (place : HeightOneSpectrum (𝓞 ℚ)) (N U : ℕ)
    (hdyadic : (finitePlacePadicPrime place : ℕ) = 2)
    (hN : N % 16 = 8)
    (hU : ¬(finitePlacePadicPrime place : ℕ) ∣ U) :
    finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (U : place.adicCompletion ℚ)) := by
  have hmod : N % 8 = 0 := by
    calc
      N % 8 = (N % 16) % 8 := (Nat.mod_mod_of_dvd N (by decide : 8 ∣ 16)).symm
      _ = 0 := by rw [hN]
  exact finiteCompletion_small_of_dyadic_nat_dvd_unit place N U hdyadic
    (Nat.dvd_of_mod_eq_zero hmod) hU

end Erdos940.Quartic
