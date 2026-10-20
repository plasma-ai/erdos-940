import Erdos940.Quartic.GaussianKummerNontrivial
import Erdos940.Quartic.GaussianTwoCharacter
import Erdos940.Quartic.GaussianDyadicNontrivial
import Erdos940.Quartic.GaussianDyadicPowerNontrivial

/-!
# Nontriviality of Gaussian quartic characters from rational radicands

An odd prime whose valuation in the radicand is not divisible by four gives
a nontrivial character witness. The test denominator is one modulo `64`, so
its power-of-two component has trivial symbol. Negative fourth powers have
a separate dyadic witness.
-/

open scoped NumberField Classical

namespace Erdos940.Quartic

/-- The odd-prime route gives a nontrivial Gaussian quartic character for an
odd signed integer outside the signed fourth powers. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_of_odd_not_signed_fourth_power
    (A : ℤ) (hA0 : A ≠ 0) (hAodd : Odd A)
    (hnot : ¬ ∃ u : ℕ,
      A = (u : ℤ) ^ 4 ∨ A = -((u : ℤ) ^ 4)) :
    ∃ b : 𝓞 GaussianField,
      b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} ∧
        ∃ hgood : GaussianQuarticGoodIdeal (A : 𝓞 GaussianField)
            (Ideal.span {b}),
          gaussianQuarticIdealSymbol (A : 𝓞 GaussianField)
            (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨p, e, s, hp, hpodd, hfac, hps, he⟩ :=
    exists_signed_odd_prime_exponent_of_not_signed_fourth_power
      hA0 hAodd hnot
  exact exists_nontrivial_gaussianQuarticIdealSymbol_of_signed_odd_prime_exponent
    A s p e hA0 hAodd hp hpodd hfac hps he

private theorem gaussianTwoPowerGoodIdeal_of_sixtyfour_congruence
    (k : ℕ) (b : 𝓞 GaussianField) (hb0 : b ≠ 0)
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) :
    GaussianQuarticGoodIdeal (((2 : ℕ) : 𝓞 GaussianField) ^ k)
      (Ideal.span {b}) := by
  have htwo := gaussianQuarticTwoGoodIdeal_of_sixtyfour_congruence b hb0 h64
  refine ⟨htwo.1, ?_⟩
  intro P hP
  refine ⟨(htwo.2 P hP).1, ?_⟩
  intro hpow
  by_cases hk : k = 0
  · subst k
    have h1 : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by simpa using hpow
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one P.asIdeal).mpr h1)
  · exact (htwo.2 P hP).2
      ((P.isPrime.pow_mem_iff_mem k (Nat.pos_of_ne_zero hk)).mp hpow)

/-- Multiplication by a power of two cannot conceal an odd-prime quartic
character: the witness denominator is chosen one modulo `64`. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_of_two_power_times_odd
    (A : ℤ) (k : ℕ) (hA0 : A ≠ 0) (hAodd : Odd A)
    (hnot : ¬ ∃ u : ℕ,
      A = (u : ℤ) ^ 4 ∨ A = -((u : ℤ) ^ 4)) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal
          ((A : 𝓞 GaussianField) * (((2 : ℕ) : 𝓞 GaussianField) ^ k))
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol
          ((A : 𝓞 GaussianField) * (((2 : ℕ) : 𝓞 GaussianField) ^ k))
          (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨b, h64, hA, hAne⟩ :=
    exists_nontrivial_gaussianQuarticIdealSymbol_of_odd_not_signed_fourth_power
      A hA0 hAodd hnot
  have hb0 := gaussian_ne_zero_of_sub_one_mem_sixtyfour b h64
  let htwo := gaussianTwoPowerGoodIdeal_of_sixtyfour_congruence k b hb0 h64
  let hprod := gaussianQuarticGoodIdeal_mul_numerator
    (A : 𝓞 GaussianField) (((2 : ℕ) : 𝓞 GaussianField) ^ k)
    (Ideal.span {b}) hA htwo
  refine ⟨b, hprod, ?_⟩
  have htwoval : gaussianQuarticIdealSymbol
      (((2 : ℕ) : 𝓞 GaussianField) ^ k)
      (Ideal.span {b}) htwo = 1 := by
    exact gaussianQuarticTwoPowerSymbol_eq_one_of_sixtyfour_congruence
      k b hb0 h64
  have hmul : gaussianQuarticIdealSymbol
      ((A : 𝓞 GaussianField) * (((2 : ℕ) : 𝓞 GaussianField) ^ k))
      (Ideal.span {b}) hprod =
        gaussianQuarticIdealSymbol (A : 𝓞 GaussianField)
          (Ideal.span {b}) hA *
          gaussianQuarticIdealSymbol (((2 : ℕ) : 𝓞 GaussianField) ^ k)
            (Ideal.span {b}) htwo :=
    gaussianQuarticIdealSymbol_mul_numerator
      (A : 𝓞 GaussianField) (((2 : ℕ) : 𝓞 GaussianField) ^ k)
      (Ideal.span {b}) hA htwo
  rw [hmul, htwoval, mul_one]
  exact hAne

/-- Every nonzero signed rational integer has an odd part and a unique
power-of-two part. This existence form is sufficient for classifying the
finite Gaussian characters. -/
theorem signedInteger_eq_two_power_mul_odd
    (R : ℤ) (hR0 : R ≠ 0) :
    ∃ k : ℕ, ∃ A : ℤ, A ≠ 0 ∧ Odd A ∧ R = (2 : ℤ) ^ k * A := by
  let n := R.natAbs
  have hn : n ≠ 0 := by simpa [n] using hR0
  let k := n.factorization 2
  let t := ordCompl[2] n
  have ht0 : t ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have htodd : Odd t := by
    have hnot2 : ¬ 2 ∣ t := Nat.not_dvd_ordCompl Nat.prime_two hn
    apply Nat.odd_iff.mpr
    omega
  have hfac : n = 2 ^ k * t :=
    (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hfac' : (n : ℤ) = (2 : ℤ) ^ k * (t : ℤ) := by
    exact_mod_cast hfac
  rcases Int.natAbs_eq R with h | h
  · exact ⟨k, (t : ℤ), by exact_mod_cast ht0, htodd.natCast,
      h.trans hfac'⟩
  · refine ⟨k, -(t : ℤ), ?_, htodd.natCast.neg, ?_⟩
    · exact neg_ne_zero.mpr (by exact_mod_cast ht0)
    · calc
        R = -(n : ℤ) := h
        _ = -((2 : ℤ) ^ k * (t : ℤ)) := congrArg Neg.neg hfac'
        _ = (2 : ℤ) ^ k * -(t : ℤ) := by ring

/-- For every nonzero rational integer, either its Gaussian quartic
character is nontrivial, or its odd part is a signed fourth power. The
latter case is exactly a signed dyadic fourth-power family. -/
theorem signedInteger_nontrivial_or_signed_dyadic_fourth_power
    (R : ℤ) (hR0 : R ≠ 0) :
    (∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1) ∨
      (∃ k u : ℕ,
        R = (2 : ℤ) ^ k * (u : ℤ) ^ 4 ∨
          R = -((2 : ℤ) ^ k * (u : ℤ) ^ 4)) := by
  obtain ⟨k, A, hA0, hAodd, hR⟩ := signedInteger_eq_two_power_mul_odd R hR0
  have hcast : (R : 𝓞 GaussianField) =
      (A : 𝓞 GaussianField) * (((2 : ℕ) : 𝓞 GaussianField) ^ k) := by
    calc
      (R : 𝓞 GaussianField) = (((2 : ℕ) : 𝓞 GaussianField) ^ k) *
          (A : 𝓞 GaussianField) := by exact_mod_cast hR
      _ = _ := by ring
  by_cases hnot : ¬ ∃ u : ℕ,
      A = (u : ℤ) ^ 4 ∨ A = -((u : ℤ) ^ 4)
  · left
    rw [hcast]
    exact exists_nontrivial_gaussianQuarticIdealSymbol_of_two_power_times_odd
      A k hA0 hAodd hnot
  · right
    push_neg at hnot
    obtain ⟨u, hu⟩ := hnot
    refine ⟨k, u, ?_⟩
    rcases hu with hu | hu
    · left
      rw [hR, hu]
    · right
      rw [hR, hu]
      ring

/-- A negative dyadic fourth-power class is nontrivial when its power of
two is divisible by four, because it is itself a negative fourth power. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_negative_dyadic_fourth_power
    (k u : ℕ) (hu : u ≠ 0) (hk : 4 ∣ k) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal
          ((-((2 : ℤ) ^ k * (u : ℤ) ^ 4) : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol
          ((-((2 : ℤ) ^ k * (u : ℤ) ^ 4) : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨q, rfl⟩ := hk
  let v : ℤ := (2 : ℤ) ^ q * (u : ℤ)
  have hv : v ≠ 0 := by
    dsimp [v]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hu)
  have hpow : -(v ^ 4) = -((2 : ℤ) ^ (4 * q) * (u : ℤ) ^ 4) := by
    dsimp [v]
    ring
  simpa only [hpow] using
    exists_nontrivial_gaussianQuarticIdealSymbol_negative_fourth_power v hv

/-- For rational-integer radicands, either a nontrivial symbol exists or the
radicand is a positive dyadic fourth-power class or a negative such class
with a dyadic exponent not divisible by four. -/
theorem signedInteger_nontrivial_or_dyadic_residual
    (R : ℤ) (hR0 : R ≠ 0) :
    (∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1) ∨
      (∃ k u : ℕ,
        R = (2 : ℤ) ^ k * (u : ℤ) ^ 4 ∨
          (R = -((2 : ℤ) ^ k * (u : ℤ) ^ 4) ∧ ¬ 4 ∣ k)) := by
  rcases signedInteger_nontrivial_or_signed_dyadic_fourth_power R hR0 with
    hw | ⟨k, u, hu | hu⟩
  · exact Or.inl hw
  · exact Or.inr ⟨k, u, Or.inl hu⟩
  · by_cases hk : 4 ∣ k
    · left
      have hu0 : u ≠ 0 := by
        intro hz
        subst u
        simp at hu
        exact hR0 hu
      have hw := exists_nontrivial_gaussianQuarticIdealSymbol_negative_dyadic_fourth_power
        k u hu0 hk
      simpa only [hu] using hw
    · exact Or.inr ⟨k, u, Or.inr ⟨hu, hk⟩⟩

/-- Apart from a positive fourth power, the residual classes have dyadic
exponents nonzero modulo four. -/
theorem signedInteger_nontrivial_or_fourth_power_or_dyadic_residual
    (R : ℤ) (hR0 : R ≠ 0) :
    (∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1) ∨
      (∃ u : ℕ, R = (u : ℤ) ^ 4) ∨
      (∃ k u : ℕ, ¬ 4 ∣ k ∧
        (R = (2 : ℤ) ^ k * (u : ℤ) ^ 4 ∨
          R = -((2 : ℤ) ^ k * (u : ℤ) ^ 4))) := by
  rcases signedInteger_nontrivial_or_dyadic_residual R hR0 with
    hw | ⟨k, u, hu | ⟨hu, hk⟩⟩
  · exact Or.inl hw
  · by_cases hk : 4 ∣ k
    · obtain ⟨q, rfl⟩ := hk
      refine Or.inr (Or.inl ⟨2 ^ q * u, ?_⟩)
      rw [hu]
      push_cast
      ring
    · exact Or.inr (Or.inr ⟨k, u, hk, Or.inl hu⟩)
  · exact Or.inr (Or.inr ⟨k, u, hk, Or.inr hu⟩)

/-- Reduce a dyadic fourth-power class to an exponent below four. -/
theorem two_power_times_fourth_power_normal_form (k u : ℕ) :
    ∃ r v : ℕ, r < 4 ∧
      (2 : ℤ) ^ k * (u : ℤ) ^ 4 = (2 : ℤ) ^ r * (v : ℤ) ^ 4 := by
  let q := k / 4
  let r := k % 4
  refine ⟨r, 2 ^ q * u, Nat.mod_lt _ (by decide), ?_⟩
  have hk : 4 * q + r = k := by
    dsimp [q, r]
    omega
  rw [← hk]
  push_cast
  ring

/-- The exceptional negative dyadic class is a fourth power in the
Gaussian integer ring: `(1+i)^4 = -4`. -/
theorem negative_four_times_fourth_power_is_gaussian_fourth_power (u : ℤ) :
    ∃ v : 𝓞 GaussianField,
      v ^ 4 = ((-4 * u ^ 4 : ℤ) : 𝓞 GaussianField) := by
  let g : GaussianInt := ⟨1, 1⟩
  have hg : g ^ 4 = -4 := by
    norm_num [g, pow_succ, Zsqrtd.ext_iff]
  let v : 𝓞 GaussianField := gaussianFourthIntegerRingEquiv g * (u : 𝓞 GaussianField)
  refine ⟨v, ?_⟩
  calc
    v ^ 4 = (gaussianFourthIntegerRingEquiv g) ^ 4 *
        (u : 𝓞 GaussianField) ^ 4 := by simp [v, mul_pow]
    _ = (gaussianFourthIntegerRingEquiv (g ^ 4)) *
        (u : 𝓞 GaussianField) ^ 4 := by rw [map_pow]
    _ = ((-4 : ℤ) : 𝓞 GaussianField) * (u : 𝓞 GaussianField) ^ 4 := by
        rw [hg]
        simp only [map_neg, map_ofNat, Int.cast_neg, Int.cast_ofNat]
    _ = ((-4 * u ^ 4 : ℤ) : 𝓞 GaussianField) := by push_cast; ring

/-- Every negative dyadic exponent congruent to two modulo four is a
Gaussian fourth power. -/
theorem negative_dyadic_fourth_class_is_gaussian_fourth_power
    (k u : ℕ) (hk : k % 4 = 2) :
    ∃ v : 𝓞 GaussianField,
      v ^ 4 = ((-((2 : ℤ) ^ k * (u : ℤ) ^ 4) : ℤ) : 𝓞 GaussianField) := by
  let q := k / 4
  have hk' : k = 4 * q + 2 := by
    dsimp [q]
    omega
  obtain ⟨v, hv⟩ :=
    negative_four_times_fourth_power_is_gaussian_fourth_power
      ((2 : ℤ) ^ q * (u : ℤ))
  refine ⟨v, ?_⟩
  rw [hv, hk']
  push_cast
  ring

/-- Unconditional classification up to the five dyadic residue classes:
the other two classes are actual fourth powers in the Gaussian ring. -/
theorem signedInteger_nontrivial_or_gaussian_fourth_power_or_five_dyadic_classes
    (R : ℤ) (hR0 : R ≠ 0) :
    (∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1) ∨
      (∃ v : 𝓞 GaussianField, v ^ 4 = (R : 𝓞 GaussianField)) ∨
      (∃ k u : ℕ, ¬ 4 ∣ k ∧
        (R = (2 : ℤ) ^ k * (u : ℤ) ^ 4 ∨
          (R = -((2 : ℤ) ^ k * (u : ℤ) ^ 4) ∧ k % 4 ≠ 2))) := by
  rcases signedInteger_nontrivial_or_fourth_power_or_dyadic_residual R hR0 with
    hw | ⟨u, hu⟩ | ⟨k, u, hk, hu | hu⟩
  · exact Or.inl hw
  · right
    left
    refine ⟨(u : 𝓞 GaussianField), ?_⟩
    rw [hu]
    push_cast
    rfl
  · exact Or.inr (Or.inr ⟨k, u, hk, Or.inl hu⟩)
  · by_cases hclass : k % 4 = 2
    · right
      left
      obtain ⟨v, hv⟩ :=
        negative_dyadic_fourth_class_is_gaussian_fourth_power k u hclass
      exact ⟨v, by simpa only [hu] using hv⟩
    · exact Or.inr (Or.inr ⟨k, u, hk, Or.inr ⟨hu, hclass⟩⟩)

/-- Every nonzero rational-integer radicand gives either a nontrivial
Gaussian quartic character or an actual fourth power in the Gaussian ring.
The dyadic residue classes are resolved by a prime of norm `5 mod 8`. -/
theorem signedInteger_nontrivial_or_gaussian_fourth_power
    (R : ℤ) (hR0 : R ≠ 0) :
    (∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1) ∨
      (∃ v : 𝓞 GaussianField, v ^ 4 = (R : 𝓞 GaussianField)) := by
  rcases signedInteger_nontrivial_or_gaussian_fourth_power_or_five_dyadic_classes
      R hR0 with hw | hfourth | ⟨k, u, hk, hu | ⟨hu, hclass⟩⟩
  · exact Or.inl hw
  · exact Or.inr hfourth
  · left
    have hu0 : (u : ℤ) ≠ 0 := by
      intro hz
      have huz : u = 0 := by exact_mod_cast hz
      subst u
      simp at hu
      exact hR0 hu
    have hw := exists_nontrivial_gaussianQuarticIdealSymbol_two_power_fourth
      (u : ℤ) hu0 k hk
    simpa only [hu] using hw

  · left
    have hu0 : (u : ℤ) ≠ 0 := by
      intro hz
      have huz : u = 0 := by exact_mod_cast hz
      subst u
      simp at hu
      exact hR0 hu
    have hodd : k % 2 = 1 := by omega
    have hw := exists_nontrivial_gaussianQuarticIdealSymbol_negative_two_power_fourth
      (u : ℤ) hu0 k hodd
    simpa only [hu] using hw

/-- A rational-integer radicand which is not a fourth power in the
Gaussian ring defines a nontrivial quartic ideal character. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_of_not_gaussian_fourth_power
    (R : ℤ) (hR0 : R ≠ 0)
    (hnot : ¬ ∃ v : 𝓞 GaussianField,
      v ^ 4 = (R : 𝓞 GaussianField)) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1 :=
  (signedInteger_nontrivial_or_gaussian_fourth_power R hR0).resolve_right hnot

end Erdos940.Quartic
