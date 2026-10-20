import Erdos940.Quartic.GaussianTwoCharacter
import Erdos940.Quartic.GaussianConductorPeriodicity
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A rational conductor for every quartic Gaussian character

Every nonzero integer is a signed power of two times an odd integer. The
odd-numerator reciprocity theorem and the dyadic Hilbert-product theorem
give a common principal modulus `64 * |R|`. This module connects that
principal statement to periodicity of the zero-extended lattice weight.
-/

open scoped NumberField
open Erdos940.Quartic.GaussianCellPartition
open Erdos940.Quartic.GaussianHeckeLBridge
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

private theorem candidate_congruence_of_two_pow_decomposition
    (N U k : ℕ) (hN : N = 2 ^ k * U)
    (b : 𝓞 GaussianField)
    (h : b - 1 ∈ gaussianQuarticConductorCandidate N) :
    b - 1 ∈ gaussianQuarticConductorCandidate U := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h
  apply Ideal.mem_span_singleton.mpr
  refine ⟨(((2 : ℕ) ^ k : ℕ) : 𝓞 GaussianField) * c, ?_⟩
  calc
    b - 1 = ((64 * N : ℕ) : 𝓞 GaussianField) * c := hc
    _ = ((64 * U : ℕ) : 𝓞 GaussianField) *
        ((((2 : ℕ) ^ k : ℕ) : 𝓞 GaussianField) * c) := by
      rw [hN]
      push_cast
      ring

/-- A positive rational quartic parameter has principal period `64N`,
including when the parameter is even. -/
theorem gaussianQuarticIdealSymbol_eq_one_of_any_congruence
    (N : ℕ) (hN0 : N ≠ 0)
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (hcong : b - 1 ∈ gaussianQuarticConductorCandidate N) :
    gaussianQuarticIdealSymbol (N : 𝓞 GaussianField) (Ideal.span {b})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (N : 𝓞 GaussianField) b hb0
          (gaussianConductorCandidate_congruences N b hcong).2
          (gaussianConductorCandidate_congruences N b hcong).1) = 1 := by
  obtain ⟨k, U, hUodd, hN⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hN0
    simp [hN, hzero]
  have hcongU := candidate_congruence_of_two_pow_decomposition
    N U k hN b hcong
  have hcomp := gaussianQuarticOddTimesSignedTwoPowerSymbol_eq_one
    U hU0 hUodd 1 (Or.inl rfl) k b hb0 hcongU
  have hcast : (N : 𝓞 GaussianField) =
      (U : 𝓞 GaussianField) *
        ((1 : 𝓞 GaussianField) * (((2 : ℕ) : 𝓞 GaussianField) ^ k)) := by
    rw [hN]
    push_cast
    ring
  simpa only [hcast] using hcomp

/-- A negative rational quartic parameter has the same principal period
as its absolute value, including when that value is even. -/
theorem gaussianQuarticIdealSymbol_eq_one_of_any_negative_congruence
    (N : ℕ) (hN0 : N ≠ 0)
    (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (hcong : b - 1 ∈ gaussianQuarticConductorCandidate N) :
    gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField)) (Ideal.span {b})
        (gaussianQuarticGoodIdeal_of_principal_congruences
          (-(N : 𝓞 GaussianField)) b hb0
          (by simpa only [Ideal.span_singleton_neg] using
            (gaussianConductorCandidate_congruences N b hcong).2)
          (gaussianConductorCandidate_congruences N b hcong).1) = 1 := by
  obtain ⟨k, U, hUodd, hN⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hU0 : U ≠ 0 := by
    intro hzero
    apply hN0
    simp [hN, hzero]
  have hcongU := candidate_congruence_of_two_pow_decomposition
    N U k hN b hcong
  have hcomp := gaussianQuarticOddTimesSignedTwoPowerSymbol_eq_one
    U hU0 hUodd (-1) (Or.inr rfl) k b hb0 hcongU
  have hcast : -(N : 𝓞 GaussianField) =
      (U : 𝓞 GaussianField) *
        ((-1 : 𝓞 GaussianField) * (((2 : ℕ) : 𝓞 GaussianField) ^ k)) := by
    rw [hN]
    push_cast
    ring
  simpa only [hcast] using hcomp

private theorem gaussianQuarticIdealSymbol_any_negative_congruent
    (N : ℕ) (hN0 : N ≠ 0)
    (b c : 𝓞 GaussianField)
    (hB : GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField)) (Ideal.span {b}))
    (hC : GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField)) (Ideal.span {c}))
    (hbc : b - c ∈ gaussianQuarticConductorCandidate N) :
    gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField)) (Ideal.span {b}) hB =
      gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField)) (Ideal.span {c}) hC := by
  have hCpos : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
      (Ideal.span {c}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mp hC
  obtain ⟨t, ht0, hct⟩ :=
    gaussianQuarticGoodIdeal_exists_inverse_candidate N hN0 c hCpos
  have hbt : b * t - 1 ∈ gaussianQuarticConductorCandidate N := by
    have hdiff : (b - c) * t ∈ gaussianQuarticConductorCandidate N :=
      (gaussianQuarticConductorCandidate N).mul_mem_right t hbc
    convert (gaussianQuarticConductorCandidate N).add_mem hdiff hct using 1 <;> ring
  have hb0 : b ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hB.1
  have hc0 : c ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hC.1
  have hBt : GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField))
      (Ideal.span {b * t}) :=
    gaussianQuarticGoodIdeal_of_principal_congruences _ _
      (mul_ne_zero hb0 ht0)
      (by simpa only [Ideal.span_singleton_neg] using
        (gaussianConductorCandidate_congruences N (b * t) hbt).2)
      (gaussianConductorCandidate_congruences N (b * t) hbt).1
  have hCt : GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField))
      (Ideal.span {c * t}) :=
    gaussianQuarticGoodIdeal_of_principal_congruences _ _
      (mul_ne_zero hc0 ht0)
      (by simpa only [Ideal.span_singleton_neg] using
        (gaussianConductorCandidate_congruences N (c * t) hct).2)
      (gaussianConductorCandidate_congruences N (c * t) hct).1
  have hBtriv : gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField))
      (Ideal.span {b * t}) hBt = 1 :=
    gaussianQuarticIdealSymbol_eq_one_of_any_negative_congruence
      N hN0 (b * t) (mul_ne_zero hb0 ht0) hbt
  have hCtriv : gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField))
      (Ideal.span {c * t}) hCt = 1 :=
    gaussianQuarticIdealSymbol_eq_one_of_any_negative_congruence
      N hN0 (c * t) (mul_ne_zero hc0 ht0) hct
  exact gaussianQuarticIdealSymbol_eq_of_products_one
    (-(N : 𝓞 GaussianField)) b c t hB hC hBt hCt ht0 hBtriv hCtriv

/-- The zero-extended quartic lattice weight of every positive rational
parameter is periodic in each Gaussian coordinate modulo `64N`. -/
theorem quarticIdealLatticeWeight_any_nat_periodic
    (N : ℕ) (hN0 : N ≠ 0) (ι : GaussianField →+* ℂ) :
    PeriodicGaussianWeight (64 * N)
      (quarticIdealLatticeWeight (N : 𝓞 GaussianField) ι) := by
  intro i j u v
  let b := gaussianPointInteger (signedCellPoint (64 * N) i j u v)
  let c := gaussianPointInteger (signedCellPoint (64 * N) 0 0 u v)
  have hbc : b - c ∈ gaussianQuarticConductorCandidate N :=
    gaussianPointInteger_signedCellPoint_congruent N i j u v
  by_cases hC : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField) (Ideal.span {c})
  · have hB : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField) (Ideal.span {b}) :=
      gaussianQuarticGoodIdeal_congruent N hN0 b c hC hbc
    have hEq : gaussianQuarticIdealSymbol (N : 𝓞 GaussianField)
        (Ideal.span {b}) hB =
        gaussianQuarticIdealSymbol (N : 𝓞 GaussianField)
          (Ideal.span {c}) hC := by
      apply gaussianQuarticIdealSymbol_congruent N hN0 b c hB hC hbc
      intro d hd0 hd
      exact gaussianQuarticIdealSymbol_eq_one_of_any_congruence N hN0 d hd0 hd
    simpa [quarticIdealLatticeWeight, b, c, hB, hC] using
      congrArg (gaussianQuarticComplexValue ι) hEq
  · have hcb : c - b ∈ gaussianQuarticConductorCandidate N := by
      convert (gaussianQuarticConductorCandidate N).neg_mem hbc using 1 <;> ring
    have hB : ¬ GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
        (Ideal.span {b}) := by
      intro hB
      exact hC (gaussianQuarticGoodIdeal_congruent N hN0 c b hB hcb)
    simp [quarticIdealLatticeWeight, b, c, hB, hC]

/-- The same period for a negative rational parameter of arbitrary parity. -/
theorem quarticIdealLatticeWeight_any_negative_nat_periodic
    (N : ℕ) (hN0 : N ≠ 0) (ι : GaussianField →+* ℂ) :
    PeriodicGaussianWeight (64 * N)
      (quarticIdealLatticeWeight (-(N : 𝓞 GaussianField)) ι) := by
  intro i j u v
  let b := gaussianPointInteger (signedCellPoint (64 * N) i j u v)
  let c := gaussianPointInteger (signedCellPoint (64 * N) 0 0 u v)
  have hbc : b - c ∈ gaussianQuarticConductorCandidate N :=
    gaussianPointInteger_signedCellPoint_congruent N i j u v
  by_cases hC : GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField))
      (Ideal.span {c})
  · have hCpos : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
        (Ideal.span {c}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mp hC
    have hBpos : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
        (Ideal.span {b}) :=
      gaussianQuarticGoodIdeal_congruent N hN0 b c hCpos hbc
    have hB : GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField))
        (Ideal.span {b}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mpr hBpos
    have hEq : gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField))
        (Ideal.span {b}) hB =
        gaussianQuarticIdealSymbol (-(N : 𝓞 GaussianField))
          (Ideal.span {c}) hC :=
      gaussianQuarticIdealSymbol_any_negative_congruent N hN0 b c hB hC hbc
    simpa [quarticIdealLatticeWeight, b, c, hB, hC] using
      congrArg (gaussianQuarticComplexValue ι) hEq
  · have hcb : c - b ∈ gaussianQuarticConductorCandidate N := by
      convert (gaussianQuarticConductorCandidate N).neg_mem hbc using 1 <;> ring
    have hB : ¬ GaussianQuarticGoodIdeal (-(N : 𝓞 GaussianField))
        (Ideal.span {b}) := by
      intro hB
      have hBpos : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
          (Ideal.span {b}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mp hB
      have hCpos : GaussianQuarticGoodIdeal (N : 𝓞 GaussianField)
          (Ideal.span {c}) :=
        gaussianQuarticGoodIdeal_congruent N hN0 c b hBpos hcb
      exact hC ((gaussianQuarticGoodIdeal_neg_iff _ _).mpr hCpos)
    simp [quarticIdealLatticeWeight, b, c, hB, hC]

/-- A single period bound for every nonzero signed rational-integer
quartic parameter. -/
theorem quarticIdealLatticeWeight_any_signed_periodic
    (R : ℤ) (hR0 : R ≠ 0) (ι : GaussianField →+* ℂ) :
    PeriodicGaussianWeight (64 * R.natAbs)
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι) := by
  obtain ⟨N, rfl | rfl⟩ := R.eq_nat_or_neg
  · have hN0 : N ≠ 0 := by exact_mod_cast hR0
    simpa using quarticIdealLatticeWeight_any_nat_periodic N hN0 ι
  · have hN0 : N ≠ 0 := by simpa using hR0
    simpa using quarticIdealLatticeWeight_any_negative_nat_periodic N hN0 ι

end Erdos940.Quartic
