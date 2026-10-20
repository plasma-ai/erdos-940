import Erdos940.Quartic.GaussianHeckeCharacters
import Erdos940.Quartic.GaussianConductor
import Erdos940.Quartic.UltrametricFourthRoot
import Mathlib.Tactic

/-!
# A normalized dyadic fourth-root equation

The congruence modulo `64` turns the fourth-root equation near `1` into a
polynomial equation with a unit linear coefficient.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

/-- Extract the Gaussian integer quotient from congruence modulo `(64)`. -/
theorem gaussian_sub_one_eq_sixtyfour_mul
    (b : 𝓞 GaussianField)
    (hb : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    ∃ t : 𝓞 GaussianField, b = 1 + 64 * t := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hb
  refine ⟨t, ?_⟩
  linear_combination ht

/-- The rescaled quartic equation has linear coefficient one. -/
noncomputable def dyadicFourthRootPolynomial (R : Type*) [CommRing R] (t : R) : Polynomial R :=
  Polynomial.X + Polynomial.C 12 * Polynomial.X ^ 2 +
    Polynomial.C 64 * Polynomial.X ^ 3 +
    Polynomial.C 128 * Polynomial.X ^ 4 - Polynomial.C (2 * t)

theorem dyadicFourthRootPolynomial_eval
    (R : Type*) [CommRing R] (t z : R) :
    (dyadicFourthRootPolynomial R t).eval z =
      z + 12 * z ^ 2 + 64 * z ^ 3 + 128 * z ^ 4 - 2 * t := by
  simp [dyadicFourthRootPolynomial]

theorem dyadicFourthRootPolynomial_derivative_zero
    (R : Type*) [CommRing R] (t : R) :
    (dyadicFourthRootPolynomial R t).derivative.eval 0 = 1 := by
  simp [dyadicFourthRootPolynomial]

/-- A zero of the normalized equation gives a fourth root of `1+64t`. -/
theorem dyadicFourthRootPolynomial_root_to_fourth_root
    (R : Type*) [CommRing R] (t z : R)
    (hz : (dyadicFourthRootPolynomial R t).eval z = 0) :
    (1 + 8 * z) ^ 4 = 1 + 64 * t := by
  rw [dyadicFourthRootPolynomial_eval] at hz
  linear_combination 32 * hz

/-- Congruence modulo rational `64` gives a fourth root in every bad
dyadic Gaussian completion. -/
theorem gaussianDyadic_exists_fourth_root
    (v : HeightOneSpectrum (𝓞 GaussianField))
    (hv : v ∈ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces
      GaussianField ⟨4, by decide⟩)
    (b : 𝓞 GaussianField)
    (hb : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    let C := (HeightOneSpectrum.adicAbv GaussianField v).Completion
    ∃ y : C, y ^ 4 = algebraMap GaussianField C (b : GaussianField) := by
  let C := (HeightOneSpectrum.adicAbv GaussianField v).Completion
  have hsmall : ‖algebraMap GaussianField C (b : GaussianField) - 1‖ <
      ‖(4 : C)‖ ^ 2 := by
    exact gaussianDyadic_norm_sub_one_lt_norm_four_sq v hv b hb
  have h4 : (4 : C) ≠ 0 := by
    intro h
    simp [h] at hsmall
    exact (not_lt_of_ge (norm_nonneg _) hsmall)
  exact exists_fourth_root_of_norm_sub_one_lt_norm_four_sq
    (algebraMap GaussianField C (b : GaussianField)) h4 hsmall

end Erdos940.Quartic
