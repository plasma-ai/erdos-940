import Erdos940.Quartic.GaussianConductorComplete
import Erdos940.Quartic.GaussianHeckeLBridge

/-!
# Periodicity of the quartic Gaussian lattice weight

The principal-congruence theorem gives equality on nonzero admissible
principal ideals. The zero-extension convention also respects congruence,
so the lattice weight has the same rational period.
-/

open scoped NumberField
open Erdos940.Quartic.GaussianCellPartition
open Erdos940.Quartic.GaussianHeckeLBridge

namespace Erdos940.Quartic

private theorem gaussianPointInteger_signedCellPoint_sub
    (q : ℕ) (i j : ℤ) (u v : Fin q) :
    gaussianPointInteger (signedCellPoint q i j u v) -
        gaussianPointInteger (signedCellPoint q 0 0 u v) =
      (q : 𝓞 GaussianField) * gaussianPointInteger (i, j) := by
  unfold gaussianPointInteger
  rw [← map_sub]
  calc
    gaussianFourthIntegerRingEquiv
        (⟨(signedCellPoint q i j u v).1, (signedCellPoint q i j u v).2⟩ -
          ⟨(signedCellPoint q 0 0 u v).1, (signedCellPoint q 0 0 u v).2⟩ : GaussianInt) =
      gaussianFourthIntegerRingEquiv ((q : GaussianInt) * ⟨i, j⟩) := by
        congr 1
        ext <;> simp [signedCellPoint] <;> ring
    _ = (q : 𝓞 GaussianField) * gaussianFourthIntegerRingEquiv ⟨i, j⟩ := by
      rw [map_mul]
      simp

theorem gaussianPointInteger_signedCellPoint_congruent
    (R : ℕ) (i j : ℤ) (u v : Fin (64 * R)) :
    gaussianPointInteger (signedCellPoint (64 * R) i j u v) -
        gaussianPointInteger (signedCellPoint (64 * R) 0 0 u v) ∈
      gaussianQuarticConductorCandidate R := by
  rw [gaussianPointInteger_signedCellPoint_sub]
  unfold gaussianQuarticConductorCandidate
  apply Ideal.mem_span_singleton.mpr
  exact ⟨gaussianPointInteger (i, j), rfl⟩

theorem gaussianQuarticIdealSymbol_eq_of_products_one
    (A b c t : 𝓞 GaussianField)
    (hB : GaussianQuarticGoodIdeal A (Ideal.span {b}))
    (hC : GaussianQuarticGoodIdeal A (Ideal.span {c}))
    (hBt : GaussianQuarticGoodIdeal A (Ideal.span {b * t}))
    (hCt : GaussianQuarticGoodIdeal A (Ideal.span {c * t}))
    (ht0 : t ≠ 0)
    (hBtriv : gaussianQuarticIdealSymbol A (Ideal.span {b * t}) hBt = 1)
    (hCtriv : gaussianQuarticIdealSymbol A (Ideal.span {c * t}) hCt = 1) :
    gaussianQuarticIdealSymbol A (Ideal.span {b}) hB =
      gaussianQuarticIdealSymbol A (Ideal.span {c}) hC := by
  have htGood : GaussianQuarticGoodIdeal A (Ideal.span {t}) := by
    apply gaussianQuarticGoodIdeal_of_dvd A _ _ hCt
      (Ideal.span_singleton_eq_bot.not.mpr ht0)
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr ⟨c, mul_comm c t⟩
  have hBmul := gaussianQuarticIdealSymbol_mul A
    (Ideal.span {b}) (Ideal.span {t}) hB htGood
  have hCmul := gaussianQuarticIdealSymbol_mul A
    (Ideal.span {c}) (Ideal.span {t}) hC htGood
  have hBprod : gaussianQuarticIdealSymbol A (Ideal.span {b}) hB *
      gaussianQuarticIdealSymbol A (Ideal.span {t}) htGood = 1 := by
    rw [← hBmul]
    simpa only [Ideal.span_singleton_mul_span_singleton] using hBtriv
  have hCprod : gaussianQuarticIdealSymbol A (Ideal.span {c}) hC *
      gaussianQuarticIdealSymbol A (Ideal.span {t}) htGood = 1 := by
    rw [← hCmul]
    simpa only [Ideal.span_singleton_mul_span_singleton] using hCtriv
  exact mul_right_cancel (hBprod.trans hCprod.symm)

theorem gaussianQuarticGoodIdeal_neg_iff
    (A : 𝓞 GaussianField) (I : Ideal (𝓞 GaussianField)) :
    GaussianQuarticGoodIdeal (-A) I ↔ GaussianQuarticGoodIdeal A I := by
  constructor
  · rintro ⟨hI, hP⟩
    refine ⟨hI, ?_⟩
    intro P hPI
    obtain ⟨hcop, hneg⟩ := hP P hPI
    refine ⟨hcop, ?_⟩
    intro hA
    exact hneg (P.asIdeal.neg_mem hA)
  · rintro ⟨hI, hP⟩
    refine ⟨hI, ?_⟩
    intro P hPI
    obtain ⟨hcop, hA⟩ := hP P hPI
    refine ⟨hcop, ?_⟩
    intro hneg
    exact hA (by simpa using P.asIdeal.neg_mem hneg)

private theorem gaussianQuarticSignedConductorCandidate_neg_nat (n : ℕ) :
    gaussianQuarticSignedConductorCandidate (-(n : ℤ)) =
      gaussianQuarticConductorCandidate n := by
  simp [gaussianQuarticSignedConductorCandidate,
    gaussianQuarticConductorCandidate, mul_neg, Ideal.span_singleton_neg]

/-- The principal-ideal quartic symbol of a negative odd rational parameter
also factors through the positive modulus `(64n)`. -/
theorem gaussianQuarticIdealSymbol_neg_nat_congruent
    (n : ℕ) (hn0 : n ≠ 0) (hnodd : Odd n)
    (b c : 𝓞 GaussianField)
    (hB : GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField)) (Ideal.span {b}))
    (hC : GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField)) (Ideal.span {c}))
    (hbc : b - c ∈ gaussianQuarticConductorCandidate n) :
    gaussianQuarticIdealSymbol (-(n : 𝓞 GaussianField)) (Ideal.span {b}) hB =
      gaussianQuarticIdealSymbol (-(n : 𝓞 GaussianField)) (Ideal.span {c}) hC := by
  have hCpos : GaussianQuarticGoodIdeal (n : 𝓞 GaussianField)
      (Ideal.span {c}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mp hC
  obtain ⟨t, ht0, hct⟩ :=
    gaussianQuarticGoodIdeal_exists_inverse_candidate n hn0 c hCpos
  have hbt : b * t - 1 ∈ gaussianQuarticConductorCandidate n := by
    have hdiff : (b - c) * t ∈ gaussianQuarticConductorCandidate n :=
      (gaussianQuarticConductorCandidate n).mul_mem_right t hbc
    convert (gaussianQuarticConductorCandidate n).add_mem hdiff hct using 1 <;> ring
  have hb0 : b ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hB.1
  have hc0 : c ≠ 0 := Ideal.span_singleton_eq_bot.not.mp hC.1
  have hbtSigned : b * t - 1 ∈
      gaussianQuarticSignedConductorCandidate (-(n : ℤ)) := by
    rw [gaussianQuarticSignedConductorCandidate_neg_nat]
    exact hbt
  have hctSigned : c * t - 1 ∈
      gaussianQuarticSignedConductorCandidate (-(n : ℤ)) := by
    rw [gaussianQuarticSignedConductorCandidate_neg_nat]
    exact hct
  have hBt : GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField))
      (Ideal.span {b * t}) :=
    gaussianQuarticGoodIdeal_of_principal_congruences _ _
      (mul_ne_zero hb0 ht0)
      (by simpa only [Int.cast_neg, Int.cast_natCast] using
        (gaussianSignedConductorCandidate_congruences _ _ hbtSigned).2)
      (gaussianSignedConductorCandidate_congruences _ _ hbtSigned).1
  have hCt : GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField))
      (Ideal.span {c * t}) :=
    gaussianQuarticGoodIdeal_of_principal_congruences _ _
      (mul_ne_zero hc0 ht0)
      (by simpa only [Int.cast_neg, Int.cast_natCast] using
        (gaussianSignedConductorCandidate_congruences _ _ hctSigned).2)
      (gaussianSignedConductorCandidate_congruences _ _ hctSigned).1
  have hnoddInt : Odd (-(n : ℤ)) := by
    have h : Odd (n : ℤ) := by exact_mod_cast hnodd
    exact h.neg
  have hn0Int : -(n : ℤ) ≠ 0 := by simpa using hn0
  have hBtriv : gaussianQuarticIdealSymbol (-(n : 𝓞 GaussianField))
      (Ideal.span {b * t}) hBt = 1 :=
    by simpa only [Int.cast_neg, Int.cast_natCast] using
      (gaussianQuarticIdealSymbol_eq_one_of_signed_odd_congruence
        (-(n : ℤ)) hn0Int hnoddInt (b * t) (mul_ne_zero hb0 ht0) hbtSigned)
  have hCtriv : gaussianQuarticIdealSymbol (-(n : 𝓞 GaussianField))
      (Ideal.span {c * t}) hCt = 1 :=
    by simpa only [Int.cast_neg, Int.cast_natCast] using
      (gaussianQuarticIdealSymbol_eq_one_of_signed_odd_congruence
        (-(n : ℤ)) hn0Int hnoddInt (c * t) (mul_ne_zero hc0 ht0) hctSigned)
  exact gaussianQuarticIdealSymbol_eq_of_products_one
    (-(n : 𝓞 GaussianField)) b c t hB hC hBt hCt ht0 hBtriv hCtriv

/-- For a nonzero odd rational radicand, the zero-extended quartic ideal
symbol is periodic in each Gaussian coordinate modulo `64R`. -/
theorem quarticIdealLatticeWeight_periodic
    (R : ℕ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) :
    PeriodicGaussianWeight (64 * R)
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι) := by
  intro i j u v
  let b := gaussianPointInteger (signedCellPoint (64 * R) i j u v)
  let c := gaussianPointInteger (signedCellPoint (64 * R) 0 0 u v)
  have hbc : b - c ∈ gaussianQuarticConductorCandidate R :=
    gaussianPointInteger_signedCellPoint_congruent R i j u v
  by_cases hC : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {c})
  · have hB : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField) (Ideal.span {b}) :=
      gaussianQuarticGoodIdeal_congruent R hR0 b c hC hbc
    have hEq : gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
        (Ideal.span {b}) hB =
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {c}) hC := by
      apply gaussianQuarticIdealSymbol_congruent R hR0 b c hB hC hbc
      intro d hd0 hd
      exact gaussianQuarticIdealSymbol_eq_one_of_congruence
        R hR0 hRodd d hd0 hd
    simpa [quarticIdealLatticeWeight, b, c, hB, hC] using
      congrArg (gaussianQuarticComplexValue ι) hEq
  · have hcb : c - b ∈ gaussianQuarticConductorCandidate R := by
      convert (gaussianQuarticConductorCandidate R).neg_mem hbc using 1 <;> ring
    have hB : ¬ GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
        (Ideal.span {b}) := by
      intro hB
      exact hC (gaussianQuarticGoodIdeal_congruent R hR0 c b hB hcb)
    simp [quarticIdealLatticeWeight, b, c, hB, hC]

/-- The same period for a negative odd rational radicand. -/
theorem quarticIdealLatticeWeight_neg_nat_periodic
    (n : ℕ) (hn0 : n ≠ 0) (hnodd : Odd n)
    (ι : GaussianField →+* ℂ) :
    PeriodicGaussianWeight (64 * n)
      (quarticIdealLatticeWeight (-(n : 𝓞 GaussianField)) ι) := by
  intro i j u v
  let b := gaussianPointInteger (signedCellPoint (64 * n) i j u v)
  let c := gaussianPointInteger (signedCellPoint (64 * n) 0 0 u v)
  have hbc : b - c ∈ gaussianQuarticConductorCandidate n :=
    gaussianPointInteger_signedCellPoint_congruent n i j u v
  by_cases hC : GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField))
      (Ideal.span {c})
  · have hCpos : GaussianQuarticGoodIdeal (n : 𝓞 GaussianField)
        (Ideal.span {c}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mp hC
    have hBpos : GaussianQuarticGoodIdeal (n : 𝓞 GaussianField)
        (Ideal.span {b}) :=
      gaussianQuarticGoodIdeal_congruent n hn0 b c hCpos hbc
    have hB : GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField))
        (Ideal.span {b}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mpr hBpos
    have hEq : gaussianQuarticIdealSymbol (-(n : 𝓞 GaussianField))
        (Ideal.span {b}) hB =
        gaussianQuarticIdealSymbol (-(n : 𝓞 GaussianField))
          (Ideal.span {c}) hC :=
      gaussianQuarticIdealSymbol_neg_nat_congruent n hn0 hnodd b c hB hC hbc
    simpa [quarticIdealLatticeWeight, b, c, hB, hC] using
      congrArg (gaussianQuarticComplexValue ι) hEq
  · have hcb : c - b ∈ gaussianQuarticConductorCandidate n := by
      convert (gaussianQuarticConductorCandidate n).neg_mem hbc using 1 <;> ring
    have hB : ¬ GaussianQuarticGoodIdeal (-(n : 𝓞 GaussianField))
        (Ideal.span {b}) := by
      intro hB
      have hBpos : GaussianQuarticGoodIdeal (n : 𝓞 GaussianField)
          (Ideal.span {b}) := (gaussianQuarticGoodIdeal_neg_iff _ _).mp hB
      have hCpos : GaussianQuarticGoodIdeal (n : 𝓞 GaussianField)
          (Ideal.span {c}) :=
        gaussianQuarticGoodIdeal_congruent n hn0 c b hBpos hcb
      exact hC ((gaussianQuarticGoodIdeal_neg_iff _ _).mpr hCpos)
    simp [quarticIdealLatticeWeight, b, c, hB, hC]

/-- A single signed formulation: the rational period depends only on the
absolute value of an odd radicand. -/
theorem quarticIdealLatticeWeight_signed_odd_periodic
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) :
    PeriodicGaussianWeight (64 * R.natAbs)
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι) := by
  obtain ⟨n, rfl | rfl⟩ := R.eq_nat_or_neg
  · have hn0 : n ≠ 0 := by exact_mod_cast hR0
    have hnodd : Odd n := by exact_mod_cast hRodd
    simpa using quarticIdealLatticeWeight_periodic n hn0 hnodd ι
  · have hn0 : n ≠ 0 := by
      simpa using hR0
    have hnoddInt : Odd (n : ℤ) := by simpa using hRodd
    have hnodd : Odd n := by exact_mod_cast hnoddInt
    simpa using quarticIdealLatticeWeight_neg_nat_periodic n hn0 hnodd ι

end Erdos940.Quartic
