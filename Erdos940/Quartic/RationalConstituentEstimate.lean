import Erdos940.Quartic.SelectorIntegration
import Erdos940.Quartic.QuadraticCharacterLBound
import Erdos940.Quartic.UniformEulerMajorant
import Erdos940.Quartic.GlobalElevenCharacter
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The rational constituent of the quartic trace

The selector supplies a negative Legendre value for every regular
coefficient tuple. This witnesses nonprincipality of the associated
rational quadratic character; its prime sum then follows from the
Dirichlet L-series estimate.
-/

namespace Erdos940.Quartic

open Finset

/-- Every rational prime through a natural cutoff, including two. -/
noncomputable def rationalPrimesLE (B : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE B).attach.image fun P =>
    (⟨P.val, (Nat.mem_primesLE.mp P.property).2⟩ : Nat.Primes)

theorem mem_rationalPrimesLE (B : ℕ) (P : Nat.Primes) :
    P ∈ rationalPrimesLE B ↔ (P : ℕ) ≤ B := by
  classical
  constructor
  · intro h
    obtain ⟨Q, _hQ, hQP⟩ := Finset.mem_image.mp h
    have hQle := (Nat.mem_primesLE.mp Q.property).1
    have heq : Q.val = (P : ℕ) := congrArg Subtype.val hQP
    simpa only [heq] using hQle
  · intro h
    let Q : (Nat.primesLE B) :=
      ⟨(P : ℕ), Nat.mem_primesLE.mpr ⟨h, P.property⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨Q, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

theorem quartic_good_prime_iff_not_dvd_product
    (d : Fin 4 → CanonicalParts) (p : ℕ) (hp : p.Prime) :
    (∀ i, ¬p ∣ (d i).val) ↔ ¬p ∣ coefficientProduct d := by
  constructor
  · intro hgood hdiv
    letI : Fact p.Prime := ⟨hp⟩
    have hunit (i : Fin 4) : ((d i).val : ZMod p) ≠ 0 := by
      intro hz
      exact hgood i ((ZMod.natCast_eq_zero_iff (d i).val p).mp hz)
    have hprod : (∏ i : Fin 4, ((d i).val : ZMod p)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hunit i)
    have hz : (coefficientProduct d : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (coefficientProduct d) p).mpr hdiv
    exact hprod (by simpa [coefficientProduct] using hz)
  · intro hnot i hdiv
    apply hnot
    exact hdiv.trans (by
      unfold coefficientProduct
      exact Finset.dvd_prod_of_mem (fun j : Fin 4 => (d j).val)
        (Finset.mem_univ i))

/-- The modulus `4D` of the rational quadratic character contributes only
a fixed amount to the logarithmic prime-sum bound. -/
theorem loglog_four_mul_coefficient_le (D : ℕ) (hD : 0 < D) :
    Real.log (Real.log (2 * (4 * D : ℕ))) ≤
      Real.log (Real.log (2 * (D : ℝ))) + Real.log 13 := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD3 : (D : ℝ) ≤ (D : ℝ) ^ 3 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hDr (by decide : 1 ≤ (3 : ℕ)))
  have hpoly : 2 * (4 * (D : ℝ)) ≤ (2 * (D : ℝ)) ^ (13 : ℕ) := by
    calc
      2 * (4 * (D : ℝ)) = 8 * (D : ℝ) := by ring
      _ ≤ 8 * (D : ℝ) ^ 3 := by gcongr
      _ = (2 * (D : ℝ)) ^ (3 : ℕ) := by ring
      _ ≤ (2 * (D : ℝ)) ^ (13 : ℕ) :=
        pow_le_pow_right₀ (by nlinarith : 1 ≤ 2 * (D : ℝ)) (by decide)
  have hQ : (1 : ℝ) ≤ (4 * D : ℕ) := by exact_mod_cast (by omega : 1 ≤ 4 * D)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (loglog_modulus_le_coefficient_loglog (D : ℝ) (4 * D : ℕ)
      hDr hQ (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hpoly))

/-- The negative-bias selector in particular supplies one negative
Legendre value at a prime coprime to the coefficient product. -/
theorem exists_negative_legendre_coefficient_product
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d) :
    ∃ p : ℕ, p.Prime ∧ p.Coprime (4 * coefficientProduct d) ∧
      quarticLegendreValue p (coefficientProduct d) = -1 := by
  classical
  let D := coefficientProduct d
  let E : Finset CanonicalParts := Finset.univ.image d
  have hd : ∀ j, d j ∈ E := by
    intro j
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hD : 0 < D := coefficientProduct_pos_for_selector d
  let w := quarticSelectorWeight D
  have hw : 0 < w := quarticSelectorWeight_pos D
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / w)
  have hTw : 1 < (T : ℝ) * w := by
    have := mul_lt_mul_of_pos_right hT hw
    have hmul : 1 / w * w = 1 := by field_simp
    linarith
  obtain ⟨Q, hQ, _hbudget, _hsquares, hfar, hbias⟩ :=
    exists_selected_quartic_coefficient_bias E D T
  have hsum : (∑ q ∈ Q,
      quarticLegendreValue q D * ((1 : ℝ) / q)) < 0 := by
    have hbound := hbias d hreg hd
    dsimp [D, w] at *
    linarith
  have hneg : ∃ q ∈ Q, quarticLegendreValue q D * ((1 : ℝ) / q) < 0 := by
    by_contra h
    push Not at h
    have hnonneg : 0 ≤ ∑ q ∈ Q,
        quarticLegendreValue q D * ((1 : ℝ) / q) := by
      apply Finset.sum_nonneg
      intro q hq
      exact h q hq
    linarith
  obtain ⟨p, hpQ, hpneg⟩ := hneg
  have hp : p.Prime := (hQ p hpQ).1
  have hpD : D < p := hfar d hreg hd p hpQ
  have hpnotD : ¬ p ∣ D := by
    intro hdiv
    have := Nat.le_of_dvd hD hdiv
    omega
  have hpnot4 : ¬ p ∣ 4 := by
    intro hdiv
    have hple : p ≤ 4 := Nat.le_of_dvd (by decide) hdiv
    have hmod := (hQ p hpQ).2.1
    interval_cases p <;> norm_num at *
  have hcop : p.Coprime (4 * D) := by
    apply (Nat.Prime.coprime_iff_not_dvd hp).2
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with h4 | hD'
    · exact hpnot4 h4
    · exact hpnotD hD'
  letI : Fact p.Prime := ⟨hp⟩
  have hlegneg : (legendreSym p D : ℝ) < 0 := by
    have hpReal : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hvalue : quarticLegendreValue p D = (legendreSym p D : ℝ) := by
      simp [quarticLegendreValue, hp]
    rw [hvalue] at hpneg
    have hrecip : 0 < (1 : ℝ) / p := by positivity
    nlinarith
  have hnonzero : ((D : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    exact hpnotD ((ZMod.natCast_eq_zero_iff D p).mp (by simpa using hz))
  rcases legendreSym.eq_one_or_neg_one p hnonzero with h | h
  · norm_num [h] at hlegneg
  · refine ⟨p, hp, hcop, ?_⟩
    simpa [quarticLegendreValue, hp, D] using
      congrArg (fun x : ℤ => (x : ℝ)) h

/-- The j=0 rational quadratic prime sum, independent of the coefficient
tuple except through its product. The selector witness removes any separate
nonprincipality assumption. -/
theorem regular_rational_legendre_prime_sum_le
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hlogB : 1 ≤ Real.log B)
    (hBelow : ∀ P ∈ S, (P : ℝ) ≤ B)
    (hCover : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ)) :
    (∑ P ∈ S,
      rationalLegendrePrimeValue (coefficientProduct d) P / (P : ℝ)) ≤
      Real.log (Real.log (2 * (coefficientProduct d : ℝ))) +
        (Real.log 13 +
          Real.log (2 + 9 / Real.log 2) +
          Real.log 4 * (1 + 1 / Real.log 2) +
          Real.log 4 * (1 + 2 / Real.log 2) +
          reciprocalSquareConstant / 2) := by
  obtain ⟨p, hp, hcop, hvalue⟩ :=
    exists_negative_legendre_coefficient_product d hreg
  letI : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p (coefficientProduct d) = -1 := by
    have hreal : (legendreSym p (coefficientProduct d) : ℝ) = -1 := by
      simpa [quarticLegendreValue, hp] using hvalue
    exact_mod_cast hreal
  have hD : 0 < coefficientProduct d := coefficientProduct_pos_for_selector d
  have hbound := rationalLegendre_prime_sum_le_loglog_four_mul
    (coefficientProduct d) hD p hcop hleg S B hB hlogB hBelow hCover
  have hmod := loglog_four_mul_coefficient_le (coefficientProduct d) hD
  linarith

/-- Primes dividing the coefficient product contribute zero to the rational
quadratic constituent. Thus the all-prime analytic sum agrees with the
good-prime sum. -/
theorem rationalLegendrePrimeValue_eq_zero_of_dvd
    (D : ℕ) (P : Nat.Primes) (hdiv : (P : ℕ) ∣ D) :
    rationalLegendrePrimeValue D P = 0 := by
  classical
  unfold rationalLegendrePrimeValue
  split_ifs with htwo
  · rfl
  · letI : Fact (P : ℕ).Prime := ⟨P.property⟩
    have hzero : legendreSym (P : ℕ) D = 0 := by
      apply (legendreSym.eq_zero_iff (P : ℕ) (D : ℤ)).mpr
      simpa using (ZMod.natCast_eq_zero_iff D (P : ℕ)).mpr hdiv
    simp [hzero]

theorem rationalLegendrePrimeSum_filter_not_dvd
    (D : ℕ) (S : Finset Nat.Primes) :
    (∑ P ∈ S.filter (fun (P : Nat.Primes) => ¬(P : ℕ) ∣ D),
      rationalLegendrePrimeValue D P / (P : ℝ)) =
    ∑ P ∈ S, rationalLegendrePrimeValue D P / (P : ℝ) := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hPS hPnot
  have hdiv : (P : ℕ) ∣ D := by
    by_contra h
    exact hPnot (Finset.mem_filter.mpr ⟨hPS, h⟩)
  simp [rationalLegendrePrimeValue_eq_zero_of_dvd D P hdiv]

private theorem base_good_sum_eq_primeSubtype_sum
    (B : ℕ) (d : Fin 4 → CanonicalParts) :
    (∑ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
      baseConstituent d 0 p / (p : ℝ)) =
    ∑ P ∈ (rationalPrimesLE B).filter
        (fun (P : Nat.Primes) => (P : ℕ) ≠ 2 ∧
          ¬(P : ℕ) ∣ coefficientProduct d),
      baseConstituent d 0 (P : ℕ) / (P : ℝ) := by
  classical
  let G := (quarticBasePrimes B).filter
    (fun p => ∀ i, ¬p ∣ (d i).val)
  let H := (rationalPrimesLE B).filter
    (fun (P : Nat.Primes) => (P : ℕ) ≠ 2 ∧
      ¬(P : ℕ) ∣ coefficientProduct d)
  change (∑ p ∈ G, baseConstituent d 0 p / (p : ℝ)) =
    ∑ P ∈ H, baseConstituent d 0 (P : ℕ) / (P : ℝ)
  refine Finset.sum_bij
    (fun p hp => (⟨p, (Finset.mem_filter.mp
      (Finset.mem_filter.mp hp).1).2⟩ : Nat.Primes)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpBase, hgood⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hpBase
    obtain ⟨hpLow, hpHigh⟩ := Finset.mem_Icc.mp hpRange
    apply Finset.mem_filter.mpr
    refine ⟨(mem_rationalPrimesLE B _).2 hpHigh, ?_, ?_⟩
    · change p ≠ 2
      omega
    · exact (quartic_good_prime_iff_not_dvd_product d p hpPrime).1 hgood
  · intro p _ q _ hpq
    exact congrArg Subtype.val hpq
  · intro P hP
    obtain ⟨hcut, hne, hnotD⟩ := Finset.mem_filter.mp hP
    have hpHigh : (P : ℕ) ≤ B := (mem_rationalPrimesLE B P).1 hcut
    have hpLow : 3 ≤ (P : ℕ) := by
      have := P.property.two_le
      omega
    have hpBase : (P : ℕ) ∈ quarticBasePrimes B :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpLow, hpHigh⟩,
        P.property⟩
    have hgood : ∀ i, ¬(P : ℕ) ∣ (d i).val :=
      (quartic_good_prime_iff_not_dvd_product d (P : ℕ) P.property).2 hnotD
    refine ⟨(P : ℕ), Finset.mem_filter.mpr ⟨hpBase, hgood⟩, ?_⟩
    apply Subtype.ext
    rfl
  · intro p hp
    rfl

/-- The j=0 estimate in the exact form required by the eleven-prime-sum
conclusion. The analytic cutoff includes the prime two, whose rational
constituent is zero; all other omitted primes divide the coefficient
product and likewise contribute zero. -/
theorem regular_baseConstituent_zero_quarticBasePrimes_le
    (B : ℕ) (hB : 3 ≤ B)
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d) :
    (∑ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
      baseConstituent d 0 p / (p : ℝ)) ≤
      Real.log (Real.log (2 * (coefficientProduct d : ℝ))) +
        (Real.log 13 +
          Real.log (2 + 9 / Real.log 2) +
          Real.log 4 * (1 + 1 / Real.log 2) +
          Real.log 4 * (1 + 2 / Real.log 2) +
          reciprocalSquareConstant / 2) := by
  classical
  let S := rationalPrimesLE B
  let G := S.filter (fun (P : Nat.Primes) =>
    ¬(P : ℕ) ∣ coefficientProduct d)
  let H := S.filter (fun (P : Nat.Primes) =>
    (P : ℕ) ≠ 2 ∧ ¬(P : ℕ) ∣ coefficientProduct d)
  have hsubset : H ⊆ G := by
    intro P hP
    obtain ⟨hPS, _, hnotD⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr ⟨hPS, hnotD⟩
  have htwo :
      (∑ P ∈ H, baseConstituent d 0 (P : ℕ) / (P : ℝ)) =
      ∑ P ∈ G, baseConstituent d 0 (P : ℕ) / (P : ℝ) := by
    apply Finset.sum_subset hsubset
    intro P hPG hPH
    obtain ⟨hPS, hnotD⟩ := Finset.mem_filter.mp hPG
    have hp2 : (P : ℕ) = 2 := by
      by_contra hne
      exact hPH (Finset.mem_filter.mpr ⟨hPS, hne, hnotD⟩)
    rw [baseConstituent_zero_eq_rationalLegendrePrimeValue_all d P]
    simp [rationalLegendrePrimeValue, hp2]
  have hBreal : (2 : ℝ) ≤ B := by exact_mod_cast (by omega : 2 ≤ B)
  have hlogB : (1 : ℝ) ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB
    have hlog3 : (1 : ℝ) ≤ Real.log 3 :=
      le_of_lt (lt_trans (by norm_num : (1 : ℝ) < 1.0986122885)
        Real.log_three_gt_d9)
    exact hlog3.trans (Real.log_le_log (by norm_num) h3)
  have hBelow (P : Nat.Primes) (hP : P ∈ S) : (P : ℝ) ≤ B := by
    exact_mod_cast (mem_rationalPrimesLE B P).1 hP
  have hCover (P : Nat.Primes) (hP : P ∉ S) :
      (B : ℝ) < P := by
    have hnot : ¬(P : ℕ) ≤ B :=
      fun h => hP ((mem_rationalPrimesLE B P).2 h)
    exact_mod_cast Nat.lt_of_not_ge hnot
  have hbound := regular_rational_legendre_prime_sum_le
    d hreg S (B : ℝ) hBreal hlogB hBelow hCover
  have heqG :
      (∑ P ∈ G, baseConstituent d 0 (P : ℕ) / (P : ℝ)) =
      ∑ P ∈ S, rationalLegendrePrimeValue (coefficientProduct d) P /
        (P : ℝ) := by
    calc
      (∑ P ∈ G, baseConstituent d 0 (P : ℕ) / (P : ℝ)) =
          ∑ P ∈ G, rationalLegendrePrimeValue (coefficientProduct d) P /
            (P : ℝ) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [baseConstituent_zero_eq_rationalLegendrePrimeValue_all d P]
      _ = _ := rationalLegendrePrimeSum_filter_not_dvd _ S
  rw [base_good_sum_eq_primeSubtype_sum B d, htwo, heqG]
  exact hbound

/-- The actual j=0 constituent of the global eleven-term base trace has
the normalized uniform finite good-prime bound. The finite set `S` covers
all primes through the cutoff; removing coefficient primes does not alter
this constituent, because its value at those primes is zero. -/
theorem regular_baseConstituent_zero_prime_sum_le
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hlogB : 1 ≤ Real.log B)
    (hBelow : ∀ P ∈ S, (P : ℝ) ≤ B)
    (hCover : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ)) :
    (∑ P ∈ S.filter (fun (P : Nat.Primes) =>
        ¬(P : ℕ) ∣ coefficientProduct d),
      baseConstituent d 0 (P : ℕ) / (P : ℝ)) ≤
      Real.log (Real.log (2 * (coefficientProduct d : ℝ))) +
        (Real.log 13 +
          Real.log (2 + 9 / Real.log 2) +
          Real.log 4 * (1 + 1 / Real.log 2) +
          Real.log 4 * (1 + 2 / Real.log 2) +
          reciprocalSquareConstant / 2) := by
  have heq : (∑ P ∈ S.filter (fun (P : Nat.Primes) =>
        ¬(P : ℕ) ∣ coefficientProduct d),
      baseConstituent d 0 (P : ℕ) / (P : ℝ)) =
      ∑ P ∈ S.filter (fun (P : Nat.Primes) =>
        ¬(P : ℕ) ∣ coefficientProduct d),
        rationalLegendrePrimeValue (coefficientProduct d) P / (P : ℝ) := by
    apply Finset.sum_congr rfl
    intro P _
    rw [baseConstituent_zero_eq_rationalLegendrePrimeValue_all d P]
  rw [heq, rationalLegendrePrimeSum_filter_not_dvd]
  exact regular_rational_legendre_prime_sum_le d hreg S B hB hlogB
    hBelow hCover

end Erdos940.Quartic
