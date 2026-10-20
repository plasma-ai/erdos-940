import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Perturbing a represented value to a local quadratic zero

If one term of a diagonal quadratic form is nonzero, a square root of
`1 - n / (a*x²)` replaces that coordinate and removes the represented value
`n`. The p-adic smallness criterion used to obtain the square root is stated
separately from this field-level algebraic step.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

/-- Hensel's inequality at `1` for `X² - (1-x)` gives a square root of `1-x`. -/
theorem padicInt_exists_sq_one_sub_of_norm_lt_two_sq
    (p : ℕ) [Fact p.Prime] (x : ℤ_[p])
    (hx : ‖x‖ < ‖(2 : ℤ_[p])‖ ^ 2) :
    ∃ s : ℤ_[p], s ^ 2 = 1 - x := by
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (1 - x)
  have heval : F.aeval (1 : ℤ_[p]) = x := by simp [F]
  have hderiv : F.derivative.aeval (1 : ℤ_[p]) = 2 := by
    simp [F]
    ring
  obtain ⟨s, hs, _, _, _⟩ := hensels_lemma (F := F) (a := (1 : ℤ_[p]))
    (by simpa [heval, hderiv] using hx)
  refine ⟨s, ?_⟩
  have hs' : s ^ 2 - (1 - x) = 0 := by simpa [F] using hs
  exact sub_eq_zero.mp hs'

/-- At an odd prime, every element of `1 + p ℤ_p` is a square. -/
theorem padicInt_exists_sq_one_sub_prime_mul
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (y : ℤ_[p]) :
    ∃ s : ℤ_[p], s ^ 2 = 1 - (p : ℤ_[p]) * y := by
  have hpNorm : ‖(p : ℤ_[p])‖ < 1 :=
    PadicInt.norm_natCast_lt_one_iff.mpr dvd_rfl
  have h2Norm : ‖(2 : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr
      (Nat.coprime_two_right.mpr
        ((Fact.out : p.Prime).odd_of_ne_two hp2))
  have hsmall : ‖(p : ℤ_[p]) * y‖ < ‖(2 : ℤ_[p])‖ ^ 2 := by
    rw [h2Norm, one_pow, norm_mul]
    calc
      ‖(p : ℤ_[p])‖ * ‖y‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one y) (norm_nonneg _)
      _ = ‖(p : ℤ_[p])‖ := mul_one _
      _ < 1 := hpNorm
  exact padicInt_exists_sq_one_sub_of_norm_lt_two_sq p _ hsmall

/-- Every element of `1 + 8 ℤ₂` is a square. -/
local instance factPrimeTwoLocalQuadraticPerturbation : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem padicInt_exists_sq_one_sub_eight_mul (y : ℤ_[2]) :
    ∃ s : ℤ_[2], s ^ 2 = 1 - (8 : ℤ_[2]) * y := by
  have h2Norm : ‖(2 : ℤ_[2])‖ = (1 / 2 : ℝ) := by
    calc
      ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by simpa using (PadicInt.norm_p (p := 2))
      _ = 1 / 2 := by norm_num
  have h8Norm : ‖(8 : ℤ_[2])‖ = (1 / 8 : ℝ) := by
    have h8 : (8 : ℤ_[2]) = (2 : ℤ_[2]) ^ 3 := by norm_num
    rw [h8, norm_pow, h2Norm]
    norm_num
  have hsmall : ‖(8 : ℤ_[2]) * y‖ < ‖(2 : ℤ_[2])‖ ^ 2 := by
    rw [h2Norm, norm_mul]
    calc
      ‖(8 : ℤ_[2])‖ * ‖y‖ ≤ ‖(8 : ℤ_[2])‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one y) (norm_nonneg _)
      _ = (1 / 8 : ℝ) := by rw [h8Norm, mul_one]
      _ < (1 / 2 : ℝ) ^ 2 := by norm_num
  exact padicInt_exists_sq_one_sub_of_norm_lt_two_sq 2 _ hsmall

theorem padic_exists_sq_one_sub_prime_mul
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (y : ℤ_[p]) :
    ∃ s : ℚ_[p], s ^ 2 = 1 - (p : ℚ_[p]) * (y : ℚ_[p]) := by
  obtain ⟨s, hs⟩ := padicInt_exists_sq_one_sub_prime_mul p hp2 y
  refine ⟨(s : ℚ_[p]), ?_⟩
  simpa using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hs

theorem padic_exists_sq_one_sub_eight_mul (y : ℤ_[2]) :
    ∃ s : ℚ_[2], s ^ 2 = 1 - (8 : ℚ_[2]) * (y : ℚ_[2]) := by
  obtain ⟨s, hs⟩ := padicInt_exists_sq_one_sub_eight_mul y
  refine ⟨(s : ℚ_[2]), ?_⟩
  have h8 : ((8 : ℤ_[2]) : ℚ_[2]) = (8 : ℚ_[2]) := by
    exact PadicInt.coe_natCast 8
  simpa [h8] using congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hs

theorem padic_exists_sq_one_sub_eight_mul_of_eq_two
    (p : ℕ) [Fact p.Prime] (hp : p = 2) (y : ℤ_[p]) :
    ∃ s : ℚ_[p], s ^ 2 = 1 - (8 : ℚ_[p]) * (y : ℚ_[p]) := by
  subst p
  exact padic_exists_sq_one_sub_eight_mul y

/-- The rational prime underlying a finite place of `ℚ`. -/
noncomputable abbrev finitePlacePadicPrime
    (place : HeightOneSpectrum (𝓞 ℚ)) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv place

local instance finitePlacePadicPrimeFact
    (place : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (finitePlacePadicPrime place : ℕ)) :=
  ⟨(finitePlacePadicPrime place).2⟩

/-- The canonical equivalence from a rational finite completion to `ℚ_p`. -/
noncomputable abbrev finitePlacePadicEquiv
    (place : HeightOneSpectrum (𝓞 ℚ)) :
    place.adicCompletion ℚ ≃A[ℚ] ℚ_[finitePlacePadicPrime place] :=
  Rat.HeightOneSpectrum.adicCompletion.padicEquiv place

/-- The valuation-small ideals used by the perturbation argument: `pℤ_p`
at odd primes and `8ℤ₂` at the dyadic place. -/
def finiteCompletionPerturbationSmall
    (place : HeightOneSpectrum (𝓞 ℚ)) (r : place.adicCompletion ℚ) : Prop :=
  ((finitePlacePadicPrime place : ℕ) ≠ 2 ∧
    ∃ y : ℤ_[finitePlacePadicPrime place],
      finitePlacePadicEquiv place r =
        (finitePlacePadicPrime place : ℚ_[finitePlacePadicPrime place]) *
          (y : ℚ_[finitePlacePadicPrime place])) ∨
  ((finitePlacePadicPrime place : ℕ) = 2 ∧
    ∃ y : ℤ_[finitePlacePadicPrime place],
      finitePlacePadicEquiv place r =
        (8 : ℚ_[finitePlacePadicPrime place]) *
          (y : ℚ_[finitePlacePadicPrime place]))

private theorem padic_nat_mul_int_ne_one
    (p m : ℕ) [Fact p.Prime] (hm : p ∣ m) (y : ℤ_[p]) :
    (m : ℚ_[p]) * (y : ℚ_[p]) ≠ 1 := by
  have hmNorm : ‖(m : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hm
  have hyNorm : ‖(y : ℚ_[p])‖ ≤ 1 := by
    simpa only [PadicInt.norm_def] using PadicInt.norm_le_one y
  have hprod : ‖(m : ℚ_[p]) * (y : ℚ_[p])‖ < 1 := by
    rw [norm_mul]
    calc
      ‖(m : ℚ_[p])‖ * ‖(y : ℚ_[p])‖ ≤ ‖(m : ℚ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left hyNorm (norm_nonneg _)
      _ = ‖(m : ℚ_[p])‖ := mul_one _
      _ < 1 := hmNorm
  intro h
  rw [h, norm_one] at hprod
  exact (lt_irrefl 1 hprod)

/-- The odd-prime and dyadic smallness ideals both give square roots in the
rational finite completion. The ideal membership is expressed after the
canonical equivalence with `ℚ_p`. -/
theorem finiteCompletion_exists_sq_one_sub_of_small
    (place : HeightOneSpectrum (𝓞 ℚ)) (r : place.adicCompletion ℚ)
    (hsmall : finiteCompletionPerturbationSmall place r) :
    ∃ s : place.adicCompletion ℚ, s ^ 2 = 1 - r := by
  classical
  let p := finitePlacePadicPrime place
  let e := finitePlacePadicEquiv place
  rcases hsmall with ⟨hp2, y, hy⟩ | ⟨hp2, y, hy⟩
  · obtain ⟨s, hs⟩ := padic_exists_sq_one_sub_prime_mul p.1 hp2 y
    refine ⟨e.symm s, ?_⟩
    apply e.injective
    simpa [e, hy] using hs
  · obtain ⟨s, hs⟩ := padic_exists_sq_one_sub_eight_mul_of_eq_two p.1 hp2 y
    refine ⟨e.symm s, ?_⟩
    apply e.injective
    simpa [e, hy] using hs

theorem finiteCompletion_small_ne_one
    (place : HeightOneSpectrum (𝓞 ℚ)) (r : place.adicCompletion ℚ)
    (hsmall : finiteCompletionPerturbationSmall place r) : r ≠ 1 := by
  classical
  let p := finitePlacePadicPrime place
  let e := finitePlacePadicEquiv place
  intro hr
  rcases hsmall with ⟨_, y, hy⟩ | ⟨hp2, y, hy⟩
  · have hne := padic_nat_mul_int_ne_one p.1 p.1 dvd_rfl y
    apply hne
    simpa [e, hr] using hy.symm
  · have hdiv : p.1 ∣ 8 := by rw [hp2]; decide
    have hne := padic_nat_mul_int_ne_one p.1 8 hdiv y
    apply hne
    simpa [e, hr] using hy.symm

/-- Alter the first coordinate of a diagonal form to turn a represented
value into a nonzero zero. -/
theorem diagonal_quadratic_perturb_first
    (K : Type*) [Field K]
    (a b c d x y z w n : K)
    (hvalue : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 = n)
    (hterm : a * x ^ 2 ≠ 0)
    (hsmall : n / (a * x ^ 2) ≠ 1)
    (hroot : ∃ u : K, u ^ 2 = 1 - n / (a * x ^ 2)) :
    ∃ X : K, X ≠ 0 ∧
      a * X ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 = 0 := by
  obtain ⟨u, hu⟩ := hroot
  have hx : x ≠ 0 := by
    intro hx
    simp [hx] at hterm
  have ha : a ≠ 0 := by
    intro ha
    simp [ha] at hterm
  have hu0 : u ≠ 0 := by
    intro hu0
    have hr : n / (a * x ^ 2) = 1 := by
      have h : 0 = 1 - n / (a * x ^ 2) := by simpa [hu0] using hu
      linear_combination h
    exact hsmall hr
  refine ⟨x * u, mul_ne_zero hx hu0, ?_⟩
  calc
    a * (x * u) ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 =
        (a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2) +
          (a * x ^ 2) * (u ^ 2 - 1) := by ring
    _ = n + (a * x ^ 2) * (u ^ 2 - 1) := by rw [hvalue]
    _ = 0 := by rw [hu]; field_simp [ha, hx]; ring

/-- The same perturbation at any of four coordinates. -/
theorem diagonal_quadratic_perturb_fin4
    (K : Type*) [Field K]
    (a z : Fin 4 → K) (i : Fin 4) (n : K)
    (hvalue : (∑ j : Fin 4, a j * z j ^ 2) = n)
    (hterm : a i * z i ^ 2 ≠ 0)
    (hsmall : n / (a i * z i ^ 2) ≠ 1)
    (hroot : ∃ u : K, u ^ 2 = 1 - n / (a i * z i ^ 2)) :
    ∃ z' : Fin 4 → K,
      z' i ≠ 0 ∧ (∑ j : Fin 4, a j * z' j ^ 2) = 0 := by
  classical
  let rest : K := ∑ j ∈ (Finset.univ : Finset (Fin 4)).erase i, a j * z j ^ 2
  have hsplit : a i * z i ^ 2 + rest = n := by
    rw [← hvalue]
    simp [rest]
  obtain ⟨X, hX, hzero⟩ := diagonal_quadratic_perturb_first
    K (a i) rest 0 0 (z i) 1 0 0 n (by simpa using hsplit) hterm hsmall hroot
  have hzero' : a i * X ^ 2 + rest = 0 := by simpa using hzero
  let z' : Fin 4 → K := Function.update z i X
  refine ⟨z', by simpa [z'] using hX, ?_⟩
  have hupdate : (fun j : Fin 4 => a j * z' j ^ 2) =
      Function.update (fun j : Fin 4 => a j * z j ^ 2) i (a i * X ^ 2) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [z', Function.update_self]
    · simp [z', Function.update_of_ne hji]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simpa [rest, Finset.erase_eq] using hzero'

/-- A sufficiently small represented value at any one nonzero coordinate
can be removed to give a nonzero zero over the finite completion. -/
theorem finiteCompletion_diagonal_quadratic_perturb_fin4
    (place : HeightOneSpectrum (𝓞 ℚ))
    (a z : Fin 4 → place.adicCompletion ℚ) (i : Fin 4)
    (n : place.adicCompletion ℚ)
    (hvalue : (∑ j : Fin 4, a j * z j ^ 2) = n)
    (hterm : a i * z i ^ 2 ≠ 0)
    (hsmall : finiteCompletionPerturbationSmall place (n / (a i * z i ^ 2))) :
    ∃ z' : Fin 4 → place.adicCompletion ℚ,
      z' i ≠ 0 ∧ (∑ j : Fin 4, a j * z' j ^ 2) = 0 := by
  exact diagonal_quadratic_perturb_fin4 (place.adicCompletion ℚ) a z i n
    hvalue hterm
    (finiteCompletion_small_ne_one place _ hsmall)
    (finiteCompletion_exists_sq_one_sub_of_small place _ hsmall)

end Erdos940.Quartic
