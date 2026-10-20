import Erdos940.Quartic.GaussianConductor
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Gaussian factorization of odd rational prime powers

An odd rational prime is unramified in the fourth cyclotomic field. We
isolate one Gaussian prime over it, then separate its exact power from a
rational radicand for the quartic CRT witness.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

private theorem gaussianPrimeOverOdd_exists
    (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
    ∃ P : HeightOneSpectrum (𝓞 GaussianField),
      P.asIdeal.LiesOver (Ideal.span {((p : ℤ) : ℤ)}) ∧
        (Ideal.absNorm P.asIdeal).Coprime 4 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (4 : ℕ) := ⟨by decide⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  let pp : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpZ : Prime (p : ℤ) := by
    exact (Int.prime_iff_natAbs_prime).2 (by simpa using hp)
  haveI : pp.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  haveI : pp.IsMaximal := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ |>.isMaximal
    (by simpa [pp] using hpZ.ne_zero)
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ := pp.nonempty_primesOver (S := 𝓞 GaussianField)
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver pp := hQover
  letI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q pp
  have hQ0 : Q ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int Q
  let P : HeightOneSpectrum (𝓞 GaussianField) := ⟨Q, hQprime, hQ0⟩
  have h2not : ((2 : ℕ) : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro h2
    have h2Z : (2 : ℤ) ∈ pp := by
      have hUnder : (2 : ℤ) ∈ Q.under ℤ := h2
      simpa only [Q.over_def pp] using hUnder
    have hpdivZ : (p : ℤ) ∣ (2 : ℤ) := by
      exact Ideal.mem_span_singleton.mp h2Z
    have hpdiv : p ∣ 2 := by exact_mod_cast hpdivZ
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv)
  exact ⟨P, hQover, gaussianPrime_coprime_four_of_two_not_mem P h2not⟩

/-- Every odd rational prime has a Gaussian prime factor occurring to the
first power; the other factor is coprime to it. -/
theorem gaussianSpanOddPrime_eq_prime_mul_coprime
    (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
    ∃ P : HeightOneSpectrum (𝓞 GaussianField),
      ∃ J : Ideal (𝓞 GaussianField),
        (Ideal.absNorm P.asIdeal).Coprime 4 ∧
          IsCoprime P.asIdeal J ∧
          Ideal.span {(p : 𝓞 GaussianField)} = P.asIdeal * J := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (4 : ℕ) := ⟨by decide⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  let pp : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpZ : Prime (p : ℤ) :=
    (Int.prime_iff_natAbs_prime).2 (by simpa using hp)
  haveI : pp.IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  haveI : pp.IsMaximal :=
    ((Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ).isMaximal
      (by simpa [pp] using hpZ.ne_zero)
  obtain ⟨P, hOver, h2⟩ := gaussianPrimeOverOdd_exists p hp hpodd
  letI : P.asIdeal.LiesOver pp := hOver
  have hpnot4 : ¬p ∣ 4 := by
    intro h
    have hp2pow : p ∣ 2 ^ 2 := by simpa only [show 2 ^ 2 = 4 by decide] using h
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2pow
    exact hpodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
  have hram : P.asIdeal.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      p GaussianField P.asIdeal hpnot4
  have hmap : Ideal.map (algebraMap ℤ (𝓞 GaussianField)) pp =
      Ideal.span {(p : 𝓞 GaussianField)} := by
    simp [pp, Ideal.map_span]
  have hpp0 : pp ≠ ⊥ := by
    simpa [pp, Ideal.span_singleton_eq_bot] using hpZ.ne_zero
  have hmap0 : Ideal.map (algebraMap ℤ (𝓞 GaussianField)) pp ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hpp0
  have hcount : Multiset.count P.asIdeal
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(p : 𝓞 GaussianField)})) = 1 := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      pp P.asIdeal hmap0] at hram
    rw [hmap] at hram
    exact hram
  have hI0 : Ideal.span {(p : 𝓞 GaussianField)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  obtain ⟨J, hcop, hfactor⟩ :=
    Ideal.eq_prime_pow_mul_coprime hI0 P.asIdeal
  rw [hcount, pow_one] at hfactor
  exact ⟨P, J, h2, Ideal.isCoprime_iff_sup_eq.mpr hcop, hfactor⟩

/-- An odd rational prime factor with exact exponent `e` separates as a
Gaussian prime-power factor with a coprime remainder. -/
theorem gaussianSignedInteger_eq_prime_pow_mul_coprime
    (R s : ℤ) (p e : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hR : R = (p : ℤ) ^ e * s) (hps : ¬ (p : ℤ) ∣ s) :
    ∃ P : HeightOneSpectrum (𝓞 GaussianField),
      ∃ J : Ideal (𝓞 GaussianField),
        (Ideal.absNorm P.asIdeal).Coprime 4 ∧
          IsCoprime P.asIdeal J ∧
          Ideal.span {(R : 𝓞 GaussianField)} = P.asIdeal ^ e * J := by
  obtain ⟨P, Jp, h2, hPJp, hpfactor⟩ :=
    gaussianSpanOddPrime_eq_prime_mul_coprime p hp hpodd
  have hPover : P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hpdiv : P.asIdeal ∣ Ideal.span {(p : 𝓞 GaussianField)} := by
      rw [hpfactor]
      exact dvd_mul_right _ _
    have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
      have hpZ : Prime (p : ℤ) :=
        (Int.prime_iff_natAbs_prime).2 (by simpa using hp)
      exact ((Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ).isMaximal
        (by simpa [Ideal.span_singleton_eq_bot] using hpZ.ne_zero)
    rw [Ideal.liesOver_iff_dvd_map P.isPrime.ne_top]
    simpa [Ideal.map_span] using hpdiv
  have hsP : (s : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro hs
    have hsZ : s ∈ Ideal.span {(p : ℤ)} := by
      have hUnder : s ∈ P.asIdeal.under ℤ := hs
      simpa only [P.asIdeal.over_def (Ideal.span {(p : ℤ)})] using hUnder
    exact hps (Ideal.mem_span_singleton.mp hsZ)
  have hPcopS : IsCoprime P.asIdeal
      (Ideal.span {(s : 𝓞 GaussianField)}) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra hsup
    have hEq : P.asIdeal ⊔ Ideal.span {(s : 𝓞 GaussianField)} = P.asIdeal :=
      (P.isMaximal.eq_of_le hsup le_sup_left).symm
    have hsLe : Ideal.span {(s : 𝓞 GaussianField)} ≤ P.asIdeal := by
      rw [← hEq]
      exact le_sup_right
    exact hsP (hsLe (Ideal.mem_span_singleton_self _))
  let J : Ideal (𝓞 GaussianField) :=
    Jp ^ e * Ideal.span {(s : 𝓞 GaussianField)}
  have hPJpow : IsCoprime P.asIdeal (Jp ^ e) := hPJp.pow_right
  have hcop : IsCoprime P.asIdeal J := hPJpow.mul_right hPcopS
  have hfactor : Ideal.span {(R : 𝓞 GaussianField)} = P.asIdeal ^ e * J := by
    calc
      Ideal.span {(R : 𝓞 GaussianField)} =
          Ideal.span {(p : 𝓞 GaussianField)} ^ e *
            Ideal.span {(s : 𝓞 GaussianField)} := by
        rw [hR]
        simp [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
      _ = (P.asIdeal * Jp) ^ e * Ideal.span {(s : 𝓞 GaussianField)} := by
        rw [hpfactor]
      _ = P.asIdeal ^ e * J := by
        simp only [J, mul_pow]
        ac_rfl
  exact ⟨P, J, h2, hcop, hfactor⟩

/-- The Gaussian factors of a nonzero odd rational integer satisfy the
admissibility and dyadic coprimality conditions for the quartic CRT witness. -/
theorem gaussianSignedOddInteger_prime_power_factor
    (R s : ℤ) (p e : ℕ) (hR0 : R ≠ 0) (hOdd : Odd R)
    (hp : p.Prime) (hpodd : p ≠ 2)
    (hR : R = (p : ℤ) ^ e * s) (hps : ¬ (p : ℤ) ∣ s)
    (he : ¬ 4 ∣ e) :
    ∃ P : HeightOneSpectrum (𝓞 GaussianField),
      ∃ J : Ideal (𝓞 GaussianField),
        (Ideal.absNorm P.asIdeal).Coprime 4 ∧
          J ≠ 0 ∧
          (∀ Q : HeightOneSpectrum (𝓞 GaussianField),
            Q.asIdeal ∣ J → (Ideal.absNorm Q.asIdeal).Coprime 4) ∧
          IsCoprime P.asIdeal J ∧
          IsCoprime P.asIdeal
            (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) ∧
          IsCoprime J
            (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) ∧
          Ideal.span {(R : 𝓞 GaussianField)} = P.asIdeal ^ e * J := by
  obtain ⟨P, J, hP2, hPJ, hfac⟩ :=
    gaussianSignedInteger_eq_prime_pow_mul_coprime R s p e hp hpodd hR hps
  have hRcast0 : (R : 𝓞 GaussianField) ≠ 0 := by
    exact_mod_cast hR0
  have hspan0 : Ideal.span {(R : 𝓞 GaussianField)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hRcast0
  have hJ0 : J ≠ 0 := by
    intro hJ
    apply hspan0
    rw [hfac, hJ, mul_zero]
  have hJdiv : J ∣ Ideal.span {(R : 𝓞 GaussianField)} := by
    rw [hfac]
    exact dvd_mul_left _ _
  have hPdiv : P.asIdeal ∣ Ideal.span {(R : 𝓞 GaussianField)} := by
    rw [hfac]
    have hepos : 0 < e := by
      by_contra h
      have hezero : e = 0 := by omega
      subst e
      exact he (dvd_zero 4)
    exact dvd_mul_of_dvd_left (dvd_pow_self P.asIdeal hepos.ne') J
  have hGood : GaussianQuarticGoodIdeal (1 : 𝓞 GaussianField)
      (Ideal.span {(R : 𝓞 GaussianField)}) := by
    apply gaussianQuarticGoodIdeal_reverse_of_odd_and_congruent
      (R : 𝓞 GaussianField) 1 hRcast0
    · obtain ⟨k, hk⟩ := hOdd.intCast (α := 𝓞 GaussianField)
      apply Ideal.mem_span_singleton.mpr
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    · simp
  have hJ2 : ∀ Q : HeightOneSpectrum (𝓞 GaussianField),
      Q.asIdeal ∣ J → (Ideal.absNorm Q.asIdeal).Coprime 4 := by
    intro Q hQ
    exact (hGood.2 Q (dvd_trans hQ hJdiv)).1
  have hR64 : IsCoprime
      (Ideal.span {(R : 𝓞 GaussianField)})
      (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).2
    have h2 : IsCoprime (R : 𝓞 GaussianField) 2 :=
      (hOdd.intCast (α := 𝓞 GaussianField)).isCoprime_two
    convert h2.pow_right (n := 6) using 1 <;> norm_num
  have hP64 := hR64.of_isCoprime_of_dvd_left hPdiv
  have hJ64 := hR64.of_isCoprime_of_dvd_left hJdiv
  exact ⟨P, J, hP2, hJ0, hJ2, hPJ, hP64, hJ64, hfac⟩

private theorem nat_fourth_power_of_factorization_divisible
    {n : ℕ} (hn : n ≠ 0)
    (hdiv : ∀ p : ℕ, p.Prime → 4 ∣ n.factorization p) :
    ∃ u : ℕ, n = u ^ 4 := by
  let factors := n.factorization.mapRange (· / 4) (Nat.zero_div 4)
  let u := factors.prod (· ^ ·)
  have hprime (p : ℕ) (hp : p ∈ factors.support) : p.Prime :=
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hfac : factors = n.factorization.mapRange (· / 4) (Nat.zero_div 4) := rfl
  refine ⟨u, ?_⟩
  apply Nat.eq_of_factorization_eq hn (by simp [u, factors])
  intro p
  rw [Nat.factorization_pow, show u.factorization = factors from
    Nat.prod_pow_factorization_eq_self hprime]
  by_cases hp : p.Prime
  · simp [factors, Nat.mul_div_cancel' (hdiv p hp)]
  · simp [factors, Nat.factorization_eq_zero_of_not_prime n hp]

/-- A nonzero odd natural number that is not a fourth power has an odd prime
factor whose exact exponent is not divisible by four. -/
theorem exists_odd_prime_exponent_of_not_fourth_power
    {n : ℕ} (hn : n ≠ 0) (hOdd : Odd n)
    (hnot : ¬ ∃ u : ℕ, n = u ^ 4) :
    ∃ p e s : ℕ, p.Prime ∧ p ≠ 2 ∧
      n = p ^ e * s ∧ ¬ p ∣ s ∧ ¬ 4 ∣ e := by
  have hex : ∃ p : ℕ, p.Prime ∧ ¬ 4 ∣ n.factorization p := by
    by_contra h
    push_neg at h
    exact hnot (nat_fourth_power_of_factorization_divisible hn h)
  obtain ⟨p, hp, he⟩ := hex
  have hpodd : p ≠ 2 := by
    intro h2
    subst p
    have hfac0 : n.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hOdd.not_two_dvd_nat
    exact he (by rw [hfac0]; exact dvd_zero 4)
  refine ⟨p, n.factorization p, ordCompl[p] n, hp, hpodd, ?_, ?_, he⟩
  · exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  · exact Nat.not_dvd_ordCompl hp hn

/-- Apart from signed fourth powers, every nonzero odd rational radicand
has an odd prime with quartically nontrivial exact exponent. -/
theorem exists_signed_odd_prime_exponent_of_not_signed_fourth_power
    {R : ℤ} (hR0 : R ≠ 0) (hOdd : Odd R)
    (hnot : ¬ ∃ u : ℕ,
      R = (u : ℤ) ^ 4 ∨ R = -((u : ℤ) ^ 4)) :
    ∃ p e : ℕ, ∃ s : ℤ, p.Prime ∧ p ≠ 2 ∧
      R = (p : ℤ) ^ e * s ∧ ¬ (p : ℤ) ∣ s ∧ ¬ 4 ∣ e := by
  have hn : R.natAbs ≠ 0 := by simpa using hR0
  have hnotNat : ¬ ∃ u : ℕ, R.natAbs = u ^ 4 := by
    rintro ⟨u, hu⟩
    have hu' : (R.natAbs : ℤ) = (u : ℤ) ^ 4 := by exact_mod_cast hu
    rcases Int.natAbs_eq R with h | h
    · exact hnot ⟨u, Or.inl (h.trans hu')⟩
    · exact hnot ⟨u, Or.inr (h.trans (congrArg Neg.neg hu'))⟩
  obtain ⟨p, e, t, hp, hpodd, hfac, hpt, he⟩ :=
    exists_odd_prime_exponent_of_not_fourth_power hn hOdd.natAbs hnotNat
  have hfac' : (R.natAbs : ℤ) = (p : ℤ) ^ e * (t : ℤ) := by
    exact_mod_cast hfac
  rcases Int.natAbs_eq R with h | h
  · refine ⟨p, e, (t : ℤ), hp, hpodd, ?_, ?_, he⟩
    · exact h.trans hfac'
    · intro hd
      exact hpt (by exact_mod_cast hd)
  · refine ⟨p, e, -(t : ℤ), hp, hpodd, ?_, ?_, he⟩
    · calc
        R = -(R.natAbs : ℤ) := h
        _ = -((p : ℤ) ^ e * (t : ℤ)) := congrArg Neg.neg hfac'
        _ = (p : ℤ) ^ e * -(t : ℤ) := by ring
    · intro hd
      have hd' : (p : ℤ) ∣ (t : ℤ) := by simpa using hd.neg_right
      exact hpt (by exact_mod_cast hd')

end Erdos940.Quartic
