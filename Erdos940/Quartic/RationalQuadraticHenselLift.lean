import Erdos940.Quartic.CanonicalParts
import Erdos940.Quartic.QuadraticHenselLift

/-!
# A rational mixed coefficient at a good odd prime

When positive natural coefficients satisfy `b = a * t²` with positive rational
`t`, the product `a * b` is a natural square, say `k²`, and `a * t = k`.
Thus the mixed diagonal quadratic form has natural coefficients
`a, c, d, 2k`, so the integral-coefficient lifting theorem applies.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

private theorem natural_cross_coefficient_of_positive_rational_ratio
    (a b : ℕ) (t : ℚ) (ha : 0 < a) (ht : 0 < t)
    (hb : (b : ℚ) = (a : ℚ) * t ^ 2) :
    ∃ k : ℕ, k ^ 2 = a * b ∧ (a : ℚ) * t = (k : ℚ) := by
  have hs : IsSquare ((a * b : ℕ) : ℚ) := by
    refine ⟨(a : ℚ) * t, ?_⟩
    calc
      ((a * b : ℕ) : ℚ) = (a : ℚ) * (b : ℚ) := by norm_cast
      _ = (a : ℚ) * ((a : ℚ) * t ^ 2) := by rw [hb]
      _ = ((a : ℚ) * t) * ((a : ℚ) * t) := by ring
  obtain ⟨k, hk⟩ := Rat.isSquare_natCast_iff.mp hs
  have hk2 : k ^ 2 = a * b := by simpa [pow_two] using hk.symm
  refine ⟨k, hk2, ?_⟩
  have hsrat : ((a : ℚ) * t) ^ 2 = ((a * b : ℕ) : ℚ) := by
    calc
      ((a : ℚ) * t) ^ 2 = (a : ℚ) * (b : ℚ) := by rw [hb]; ring
      _ = ((a * b : ℕ) : ℚ) := by norm_cast
  have hkrat : (k : ℚ) ^ 2 = ((a * b : ℕ) : ℚ) := by exact_mod_cast hk2
  have hpos : 0 ≤ (a : ℚ) * t := le_of_lt (mul_pos (by exact_mod_cast ha) ht)
  have hkpos : (0 : ℚ) ≤ k := by positivity
  nlinarith

/-- At a good odd prime, the positive mixed-exceptional diagonal quadratic
form with rational parameter has a nontrivial zero over the completion. -/
theorem finiteCompletion_mixed_quadratic_nontrivial_zero_of_odd_good_prime
    (place : HeightOneSpectrum (𝓞 ℚ))
    (a b c d : CanonicalParts) (t : ℚ)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hgood : ∀ e ∈ ({a, b, c, d} : Finset CanonicalParts),
      ¬(finitePlacePadicPrime place : ℕ) ∣ e.val)
    (ht : 0 < t)
    (hb : (b.val : ℚ) = (a.val : ℚ) * t ^ 2) :
    ∃ q : Fin 4 → place.adicCompletion ℚ,
      (∃ i, q i ≠ 0) ∧
        (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
          (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
          (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
          ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 := by
  classical
  let p : ℕ := finitePlacePadicPrime place
  have hp : p.Prime := (finitePlacePadicPrime place).2
  have haGood : ¬p ∣ a.val := hgood a (by simp)
  have hbGood : ¬p ∣ b.val := hgood b (by simp)
  have hcGood : ¬p ∣ c.val := hgood c (by simp)
  have hdGood : ¬p ∣ d.val := hgood d (by simp)
  obtain ⟨k, hk2, hcross⟩ :=
    natural_cross_coefficient_of_positive_rational_ratio
      a.val b.val t a.property.pos ht hb
  have hkGood : ¬p ∣ k := by
    intro hpk
    have hprod : p ∣ a.val * b.val := by
      rw [← hk2]
      rcases hpk with ⟨m, hm⟩
      refine ⟨m * k, ?_⟩
      calc
        k ^ 2 = k * k := by ring
        _ = (p * m) * k := by rw [← hm]
        _ = p * (m * k) := by ring
    rcases hp.dvd_mul.mp hprod with hpa | hpb
    · exact haGood hpa
    · exact hbGood hpb
  have htwoGood : ¬p ∣ 2 := by
    intro hp2
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
  have hfourthGood : ¬p ∣ 2 * k := by
    intro hpk
    rcases hp.dvd_mul.mp hpk with hp2 | hpk'
    · exact htwoGood hp2
    · exact hkGood hpk'
  let coeff : Fin 4 → ℕ := ![a.val, c.val, d.val, 2 * k]
  have hcoeff : ∀ i, ¬p ∣ coeff i := by
    intro i
    fin_cases i <;> simp only [coeff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
      assumption
  obtain ⟨q, hnonzero, hzero⟩ :=
    finiteCompletion_quadratic_nontrivial_zero_of_odd_good_prime
      place hodd coeff hcoeff
  have hcross2 : (2 * (a.val : ℚ) * t : ℚ) = (2 * k : ℕ) := by
    calc
      2 * (a.val : ℚ) * t = 2 * ((a.val : ℚ) * t) := by ring
      _ = 2 * (k : ℚ) := by rw [hcross]
      _ = (2 * k : ℕ) := by norm_cast
  have hcrossK : ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) =
      (2 * k : ℕ) := by
    rw [hcross2]
    norm_cast
  refine ⟨q, hnonzero, ?_⟩
  rw [hcrossK]
  simpa [Fin.sum_univ_four, coeff] using hzero

end Erdos940.Quartic
