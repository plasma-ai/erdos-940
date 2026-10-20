import Erdos940.Quartic.GaussianDyadicNontrivial
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Dyadic quartic classes in the Gaussian field

At a Gaussian prime of rational norm `5 mod 8`, the quartic symbol of `2`
has order four. This detects the dyadic Kummer classes represented by
`2`, `-2`, `4`, `8`, and `-8` after multiplication by a rational fourth
power. The apparent sixth class, `-4`, is exceptional: it is the Gaussian
fourth power `(1+i)^4`.
-/

namespace Erdos940.Quartic

open scoped BigOperators
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols

attribute [local instance] Ideal.Quotient.field

/-- The rational integer `2` is not in a Gaussian prime of norm `5 mod 8`. -/
theorem gaussian_two_not_mem_of_norm_mod_eight
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5) :
    (2 : 𝓞 GaussianField) ∉ P.asIdeal := by
  classical
  letI : Fintype (𝓞 GaussianField ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 GaussianField ⧸ P.asIdeal) =
      Ideal.absNorm P.asIdeal := card_primeIdealResidueField GaussianField P
  have hchar : ringChar (𝓞 GaussianField ⧸ P.asIdeal) ≠ 2 := by
    intro h
    have heven := FiniteField.even_card_of_char_two h
    omega
  intro htwo
  have hzero : (2 : 𝓞 GaussianField ⧸ P.asIdeal) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 htwo
  exact Ring.two_ne_zero hchar hzero

/-- The quartic character of `2` has order four at primes of rational
norm `5 mod 8`. We use the supplementary law for the quadratic character
of two in a finite field. -/
theorem gaussianQuarticPrimeSymbol_two_sq_ne_one_of_norm_mod_eight
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
      gaussian_two_not_mem_of_norm_mod_eight P hmod
    gaussianQuarticPrimeSymbol 2 P h2 htwo ^ 2 ≠ 1 := by
  classical
  letI : Fintype (𝓞 GaussianField ⧸ P.asIdeal) := Fintype.ofFinite _
  let k := 𝓞 GaussianField ⧸ P.asIdeal
  have hcard : Fintype.card k = Ideal.absNorm P.asIdeal :=
    card_primeIdealResidueField GaussianField P
  have hchar : ringChar k ≠ 2 := by
    intro h
    have heven := FiniteField.even_card_of_char_two h
    omega
  have hgauss : (2 : k) ^ (Fintype.card k / 2) = -1 := by
    rw [FiniteField.two_pow_card hchar, ZMod.χ₈_nat_eq_if_mod_eight]
    have hmod2 : Ideal.absNorm P.asIdeal % 2 = 1 := by omega
    simp [hcard, hmod, hmod2]
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussian_two_not_mem_of_norm_mod_eight P hmod
  change gaussianQuarticPrimeSymbol 2 P h2 htwo ^ 2 ≠ 1
  intro hsymbol
  have hred := gaussianQuarticPrimeSymbol_reduction 2 P h2 htwo
  have hn : 4 ∣ Fintype.card k - 1 := by
    rw [hcard]
    exact dvd_absNorm_sub_one_of_primitiveRoots GaussianField P
      dyadicQuarticLevel dyadicPrimitiveFourthRoots h2
  let f := rootsOfUnityReductionEquiv GaussianField P dyadicQuarticLevel
    dyadicPrimitiveFourthRoots h2
  have hsymbol' : (gaussianQuarticPrimeSymbol 2 P h2 htwo :
      rootsOfUnity (dyadicQuarticLevel : ℕ) (𝓞 GaussianField)) ^ 2 = 1 :=
    hsymbol
  have hred0 : f (gaussianQuarticPrimeSymbol 2 P h2 htwo) =
      finiteFieldPowerResidueSymbol k dyadicQuarticLevel hn
        (primeIdealResidueUnit GaussianField P 2 htwo) := hred
  have hmap : (f (gaussianQuarticPrimeSymbol 2 P h2 htwo)) ^ 2 =
      f ((gaussianQuarticPrimeSymbol 2 P h2 htwo :
        rootsOfUnity (dyadicQuarticLevel : ℕ) (𝓞 GaussianField)) ^ 2) :=
    (map_pow f _ 2).symm
  have hcong : f ((gaussianQuarticPrimeSymbol 2 P h2 htwo :
      rootsOfUnity (dyadicQuarticLevel : ℕ) (𝓞 GaussianField)) ^ 2) = f 1 :=
    congrArg f hsymbol'
  have hfsq : (finiteFieldPowerResidueSymbol k dyadicQuarticLevel hn
      (primeIdealResidueUnit GaussianField P 2 htwo)) ^ 2 = 1 := by
    exact (congrArg (fun z : rootsOfUnity 4 k => z ^ 2) hred0.symm).trans
      (hmap.trans (hcong.trans (map_one f)))
  have hvalue : (primeIdealResidueUnit GaussianField P 2 htwo : k) = 2 := rfl
  have hh := congrArg (fun z : rootsOfUnity 4 k => ((z : kˣ) : k)) hfsq
  change ((primeIdealResidueUnit GaussianField P 2 htwo : k) ^
      ((Fintype.card k - 1) / 4)) ^ 2 = 1 at hh
  rw [hvalue, ← pow_mul, show ((Fintype.card k - 1) / 4) * 2 =
    Fintype.card k / 2 by omega, hgauss] at hh
  exact Ring.neg_one_ne_one_of_char_ne_two hchar hh

/-- Multiplicativity of the quartic prime symbol in its numerator. -/
theorem gaussianQuarticPrimeSymbol_mul_numerator
    (a b : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (ha : a ∉ P.asIdeal) (hb : b ∉ P.asIdeal) :
    gaussianQuarticPrimeSymbol (a * b) P h2
      (fun h => (P.isPrime.mem_or_mem h).elim ha hb) =
      gaussianQuarticPrimeSymbol a P h2 ha *
        gaussianQuarticPrimeSymbol b P h2 hb := by
  let hab : a * b ∉ P.asIdeal :=
    fun h => (P.isPrime.mem_or_mem h).elim ha hb
  have hm := gaussianQuarticIdealSymbol_mul_numerator a b P.asIdeal
    (gaussianQuarticGoodIdeal_prime a P h2 ha)
    (gaussianQuarticGoodIdeal_prime b P h2 hb)
  change gaussianQuarticIdealSymbol (a * b) P.asIdeal
      (gaussianQuarticGoodIdeal_prime (a * b) P h2 hab) =
    gaussianQuarticIdealSymbol a P.asIdeal
      (gaussianQuarticGoodIdeal_prime a P h2 ha) *
    gaussianQuarticIdealSymbol b P.asIdeal
      (gaussianQuarticGoodIdeal_prime b P h2 hb) at hm
  rw [gaussianQuarticIdealSymbol_prime (a * b) P h2 hab,
    gaussianQuarticIdealSymbol_prime a P h2 ha,
    gaussianQuarticIdealSymbol_prime b P h2 hb] at hm
  exact hm

/-- Powers of an admissible numerator give powers of its quartic symbol. -/
theorem gaussianQuarticPrimeSymbol_pow_numerator
    (a : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (ha : a ∉ P.asIdeal) (n : ℕ) :
    gaussianQuarticPrimeSymbol (a ^ n) P h2
      (fun h => ha (P.isPrime.mem_of_pow_mem n h)) =
      (gaussianQuarticPrimeSymbol a P h2 ha) ^ n := by
  induction n with
  | zero =>
      have hone : (1 : 𝓞 GaussianField) ∉ P.asIdeal := by
        intro h
        exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
      have h := gaussianQuarticPrimeSymbol_fourth_power_eq_one 1 P h2 hone
      simpa using h
  | succ n ih =>
      have han : a ^ n ∉ P.asIdeal :=
        fun h => ha (P.isPrime.mem_of_pow_mem n h)
      have hm := gaussianQuarticPrimeSymbol_mul_numerator
        (a ^ n) a P h2 han ha
      rw [ih] at hm
      simpa only [pow_succ] using hm

/-- Exact order of the supplementary quartic character of two. -/
theorem gaussianQuarticPrimeSymbol_two_order_four_of_norm_mod_eight
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
      gaussian_two_not_mem_of_norm_mod_eight P hmod
    orderOf (gaussianQuarticPrimeSymbol 2 P h2 htwo) = 4 := by
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussian_two_not_mem_of_norm_mod_eight P hmod
  let s := gaussianQuarticPrimeSymbol 2 P h2 htwo
  have hs4 : s ^ 4 = 1 := by
    apply Subtype.ext
    exact s.property
  have hs2 : s ^ 2 ≠ 1 :=
    gaussianQuarticPrimeSymbol_two_sq_ne_one_of_norm_mod_eight P hmod
  have hd4 : orderOf s ∣ 4 := orderOf_dvd_of_pow_eq_one hs4
  have hnd2 : ¬ orderOf s ∣ 2 := by
    intro h
    exact hs2 (orderOf_dvd_iff_pow_eq_one.mp h)
  change orderOf s = 4
  have hpos : 0 < orderOf s := orderOf_pos s
  have hle : orderOf s ≤ 4 := Nat.le_of_dvd (by decide) hd4
  interval_cases h : orderOf s <;> norm_num at *

theorem gaussianQuarticPrimeSymbol_two_pow_ne_one_of_norm_mod_eight
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5)
    (k : ℕ) (hk : ¬ 4 ∣ k) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
      gaussian_two_not_mem_of_norm_mod_eight P hmod
    (gaussianQuarticPrimeSymbol 2 P h2 htwo) ^ k ≠ 1 := by
  have horder := gaussianQuarticPrimeSymbol_two_order_four_of_norm_mod_eight
    P hmod
  change (gaussianQuarticPrimeSymbol 2 P _ _) ^ k ≠ 1
  intro h
  exact hk (horder ▸ orderOf_dvd_of_pow_eq_one h)

theorem gaussianQuarticPrimeSymbol_negative_one_sq_eq_one
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4) :
    let hneg : (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
      intro hm
      have hone : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
        simpa using P.asIdeal.neg_mem hm
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    (gaussianQuarticPrimeSymbol (-1) P h2 hneg) ^ 2 = 1 := by
  have hneg : (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro hm
    have hone : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
      simpa using P.asIdeal.neg_mem hm
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  have hone : (1 : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hsymOne := gaussianQuarticPrimeSymbol_fourth_power_eq_one 1 P h2 hone
  have hsymPow := gaussianQuarticPrimeSymbol_pow_numerator (-1) P h2 hneg 2
  change (gaussianQuarticPrimeSymbol (-1) P h2 hneg) ^ 2 = 1
  simpa only [neg_one_sq] using hsymPow.symm.trans (by simpa using hsymOne)

/-- The positive dyadic classes with exponent not divisible by four are
detected at any Gaussian prime of norm `5 mod 8` away from `u`. -/
theorem gaussianQuarticPrimeSymbol_two_power_fourth_ne_one
    (u : ℤ) (k : ℕ) (hk : ¬ 4 ∣ k)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5)
    (hu : (u : 𝓞 GaussianField) ∉ P.asIdeal) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let hR : (2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4 ∉
        P.asIdeal := by
      intro h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact gaussian_two_not_mem_of_norm_mod_eight P hmod
          (P.isPrime.mem_of_pow_mem k h)
      · exact hu (P.isPrime.mem_of_pow_mem 4 h)
    gaussianQuarticPrimeSymbol
      ((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4)
      P h2 hR ≠ 1 := by
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussian_two_not_mem_of_norm_mod_eight P hmod
  have htwoPow : (2 : 𝓞 GaussianField) ^ k ∉ P.asIdeal :=
    fun h => htwo (P.isPrime.mem_of_pow_mem k h)
  have huPow : (u : 𝓞 GaussianField) ^ 4 ∉ P.asIdeal :=
    fun h => hu (P.isPrime.mem_of_pow_mem 4 h)
  have hR : (2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4 ∉
      P.asIdeal :=
    fun h => (P.isPrime.mem_or_mem h).elim htwoPow huPow
  have hm := gaussianQuarticPrimeSymbol_mul_numerator
    ((2 : 𝓞 GaussianField) ^ k) ((u : 𝓞 GaussianField) ^ 4)
    P h2 htwoPow huPow
  have hpow := gaussianQuarticPrimeSymbol_pow_numerator 2 P h2 htwo k
  have hu4 := gaussianQuarticPrimeSymbol_fourth_power_eq_one
    (u : 𝓞 GaussianField) P h2 hu
  have hne := gaussianQuarticPrimeSymbol_two_pow_ne_one_of_norm_mod_eight
    P hmod k hk
  change gaussianQuarticPrimeSymbol
    ((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4)
    P h2 hR ≠ 1
  intro heq
  rw [hpow, hu4, mul_one] at hm
  exact hne (hm.symm.trans heq)

/-- For odd dyadic exponent, multiplication by `-1` cannot cancel the
quartic character of two: the former has order at most two, the latter
has order four. -/
theorem gaussianQuarticPrimeSymbol_negative_two_power_fourth_ne_one
    (u : ℤ) (k : ℕ) (hk : k % 2 = 1)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5)
    (hu : (u : 𝓞 GaussianField) ∉ P.asIdeal) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let hR : -((2 : 𝓞 GaussianField) ^ k *
        (u : 𝓞 GaussianField) ^ 4) ∉ P.asIdeal := by
      intro h
      have hprod := P.asIdeal.neg_mem h
      rcases P.isPrime.mem_or_mem (by simpa using hprod) with h | h
      · exact gaussian_two_not_mem_of_norm_mod_eight P hmod
          (P.isPrime.mem_of_pow_mem k h)
      · exact hu (P.isPrime.mem_of_pow_mem 4 h)
    gaussianQuarticPrimeSymbol
      (-((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4))
      P h2 hR ≠ 1 := by
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussian_two_not_mem_of_norm_mod_eight P hmod
  have htwoPow : (2 : 𝓞 GaussianField) ^ k ∉ P.asIdeal :=
    fun h => htwo (P.isPrime.mem_of_pow_mem k h)
  have huPow : (u : 𝓞 GaussianField) ^ 4 ∉ P.asIdeal :=
    fun h => hu (P.isPrime.mem_of_pow_mem 4 h)
  let v : 𝓞 GaussianField :=
    (2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4
  have hv : v ∉ P.asIdeal :=
    fun h => (P.isPrime.mem_or_mem h).elim htwoPow huPow
  have hneg : (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro hm
    have hone : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
      simpa using P.asIdeal.neg_mem hm
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  have hR : -v ∉ P.asIdeal := by
    intro h
    exact hv (by simpa using P.asIdeal.neg_mem h)
  have hmulPos := gaussianQuarticPrimeSymbol_mul_numerator
    ((2 : 𝓞 GaussianField) ^ k) ((u : 𝓞 GaussianField) ^ 4)
    P h2 htwoPow huPow
  have hpow := gaussianQuarticPrimeSymbol_pow_numerator 2 P h2 htwo k
  have hu4 := gaussianQuarticPrimeSymbol_fourth_power_eq_one
    (u : 𝓞 GaussianField) P h2 hu
  have hpos : gaussianQuarticPrimeSymbol v P h2 hv =
      (gaussianQuarticPrimeSymbol 2 P h2 htwo) ^ k := by
    simpa only [v, hpow, hu4, mul_one] using hmulPos
  have hmulNeg := gaussianQuarticPrimeSymbol_mul_numerator
    (-1) v P h2 hneg hv
  have hmulNeg' : gaussianQuarticPrimeSymbol (-v) P h2 hR =
      gaussianQuarticPrimeSymbol (-1) P h2 hneg *
        gaussianQuarticPrimeSymbol v P h2 hv := by
    simpa only [neg_one_mul] using hmulNeg
  have hnegSq := gaussianQuarticPrimeSymbol_negative_one_sq_eq_one P h2
  have hnot4 : ¬ 4 ∣ 2 * k := by omega
  have htwoNe := gaussianQuarticPrimeSymbol_two_pow_ne_one_of_norm_mod_eight
    P hmod (2 * k) hnot4
  change gaussianQuarticPrimeSymbol (-v) P h2 hR ≠ 1
  intro heq
  have hprod : gaussianQuarticPrimeSymbol (-1) P h2 hneg *
      gaussianQuarticPrimeSymbol v P h2 hv = 1 := by
    exact hmulNeg'.symm.trans heq
  have hsq := congrArg (fun z : rootsOfUnity 4 (𝓞 GaussianField) => z ^ 2) hprod
  have hmulSq := mul_pow (gaussianQuarticPrimeSymbol (-1) P h2 hneg)
    (gaussianQuarticPrimeSymbol v P h2 hv) 2
  have hvSq : (gaussianQuarticPrimeSymbol v P h2 hv) ^ 2 = 1 := by
    have hh := hmulSq.symm.trans hsq
    rw [hnegSq, one_mul] at hh
    exact hh.trans (one_pow 2)
  have hsq' : (gaussianQuarticPrimeSymbol 2 P h2 htwo) ^ (2 * k) = 1 := by
    simpa only [hpos, ← pow_mul, mul_comm] using hvSq
  exact htwoNe hsq'

/-- Every positive rational dyadic class not divisible by four has a
nontrivial quartic symbol on a principal Gaussian ideal. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_two_power_fourth
    (u : ℤ) (hu : u ≠ 0) (k : ℕ) (hk : ¬ 4 ∣ k) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal
          (((2 : ℤ) ^ k * u ^ 4 : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol
          (((2 : ℤ) ^ k * u ^ 4 : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨P, π, hmod, huP, hspan⟩ :=
    exists_gaussian_prime_avoiding_integer_mod_eight u hu
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussian_two_not_mem_of_norm_mod_eight P hmod
  have hR : (2 : 𝓞 GaussianField) ^ k *
      (u : 𝓞 GaussianField) ^ 4 ∉ P.asIdeal := by
    intro h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact htwo (P.isPrime.mem_of_pow_mem k h)
    · exact huP (P.isPrime.mem_of_pow_mem 4 h)
  have hcast : ((((2 : ℤ) ^ k * u ^ 4) : ℤ) : 𝓞 GaussianField) =
      (2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4 := by
    push_cast
    rfl
  let b : 𝓞 GaussianField := gaussianFourthIntegerRingEquiv π
  have hgood : GaussianQuarticGoodIdeal
      (((2 : ℤ) ^ k * u ^ 4 : ℤ) : 𝓞 GaussianField)
      (Ideal.span {b}) := by
    rw [hcast, ← hspan]
    exact gaussianQuarticGoodIdeal_prime _ P h2 hR
  refine ⟨b, hgood, ?_⟩
  have hprime : gaussianQuarticPrimeSymbol
      ((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4)
      P h2 hR ≠ 1 :=
    gaussianQuarticPrimeSymbol_two_power_fourth_ne_one u k hk P hmod huP
  have hprimeIdeal : gaussianQuarticIdealSymbol
      ((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4)
      P.asIdeal (gaussianQuarticGoodIdeal_prime _ P h2 hR) ≠ 1 := by
    rw [gaussianQuarticIdealSymbol_prime]
    exact hprime
  simpa only [hcast, hspan] using hprimeIdeal

/-- Every negative rational dyadic class of odd exponent has a
nontrivial quartic symbol on a principal Gaussian ideal. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_negative_two_power_fourth
    (u : ℤ) (hu : u ≠ 0) (k : ℕ) (hk : k % 2 = 1) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal
          ((-((2 : ℤ) ^ k * u ^ 4) : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol
          ((-((2 : ℤ) ^ k * u ^ 4) : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨P, π, hmod, huP, hspan⟩ :=
    exists_gaussian_prime_avoiding_integer_mod_eight u hu
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  let htwo : (2 : 𝓞 GaussianField) ∉ P.asIdeal :=
    gaussian_two_not_mem_of_norm_mod_eight P hmod
  have hR : -((2 : 𝓞 GaussianField) ^ k *
      (u : 𝓞 GaussianField) ^ 4) ∉ P.asIdeal := by
    intro h
    have hprod := P.asIdeal.neg_mem h
    rcases P.isPrime.mem_or_mem (by simpa using hprod) with h | h
    · exact htwo (P.isPrime.mem_of_pow_mem k h)
    · exact huP (P.isPrime.mem_of_pow_mem 4 h)
  have hcast : ((-((2 : ℤ) ^ k * u ^ 4) : ℤ) : 𝓞 GaussianField) =
      -((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4) := by
    push_cast
    rfl
  let b : 𝓞 GaussianField := gaussianFourthIntegerRingEquiv π
  have hgood : GaussianQuarticGoodIdeal
      ((-((2 : ℤ) ^ k * u ^ 4) : ℤ) : 𝓞 GaussianField)
      (Ideal.span {b}) := by
    rw [hcast, ← hspan]
    exact gaussianQuarticGoodIdeal_prime _ P h2 hR
  refine ⟨b, hgood, ?_⟩
  have hprime : gaussianQuarticPrimeSymbol
      (-((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4))
      P h2 hR ≠ 1 :=
    gaussianQuarticPrimeSymbol_negative_two_power_fourth_ne_one
      u k hk P hmod huP
  have hprimeIdeal : gaussianQuarticIdealSymbol
      (-((2 : 𝓞 GaussianField) ^ k * (u : 𝓞 GaussianField) ^ 4))
      P.asIdeal (gaussianQuarticGoodIdeal_prime _ P h2 hR) ≠ 1 := by
    rw [gaussianQuarticIdealSymbol_prime]
    exact hprime
  simpa only [hcast, hspan] using hprimeIdeal

end Erdos940.Quartic
