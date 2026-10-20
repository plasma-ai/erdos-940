import Erdos940.Quartic.GaussianHeckeCharacters
import Erdos940.Quartic.GaussianConductor
import Erdos940.Quartic.GaussianDyadicFourthRoot
import Erdos940.Quartic.GaussianRationalFactorization
import CebotarevDensity.Main
import ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerNormPowerClassDegree
import ClassFieldTheory.Theorems.HilbertSymbols.PowerClassEqOneIff
import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField

/-!
# Nontrivial quartic symbols from a prime-power factor

CRT isolates a Gaussian prime factor whose exponent is not divisible by four;
quartic reciprocity then moves the nontrivial value to a principal denominator.
Separately, Kummer theory and Chebotarev give infinitely many nonidentity
Frobenius primes for an arbitrary nonpower radicand. A comparison between these
Frobenius values and the quartic residue symbol is not supplied here.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

set_option maxHeartbeats 1000000
attribute [local instance] Ideal.Quotient.field

noncomputable section

/-- The quartic residue symbol of a finite field containing fourth roots of
unity takes a nonidentity value. -/
theorem exists_finiteFieldQuarticSymbol_ne_one
    (k : Type*) [Field k] [Fintype k]
    (h4 : 4 ∣ Fintype.card k - 1) :
    ∃ u : kˣ,
      AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        k (⟨4, by decide⟩ : ℕ+) h4 u ≠ 1 := by
  classical
  let n : ℕ+ := ⟨4, by decide⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  refine ⟨g, ?_⟩
  intro hsymbol
  have hpow : g ^ ((Fintype.card k - 1) / 4) = 1 := by
    have h := congrArg
      (fun z : rootsOfUnity (n : ℕ) k => (z : kˣ)) hsymbol
    exact h
  have horder : orderOf g = Fintype.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, Fintype.card_units]
  have hdvd : Fintype.card k - 1 ∣ (Fintype.card k - 1) / 4 := by
    have hdvd0 : orderOf g ∣ (Fintype.card k - 1) / 4 :=
      orderOf_dvd_iff_pow_eq_one.mpr hpow
    simpa only [horder] using hdvd0
  have hpos : 0 < Fintype.card k - 1 := by
    have h : 0 < Nat.card kˣ := Nat.card_pos
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h
  have hquotPos : 0 < (Fintype.card k - 1) / 4 := by
    exact Nat.div_pos (Nat.le_of_dvd hpos h4) (by decide)
  exact (Nat.not_le_of_gt (Nat.div_lt_self hpos (by decide)))
    (Nat.le_of_dvd hquotPos hdvd)

/-- A generator of the finite-field unit group has a quartic symbol of
order exactly four. -/
theorem exists_finiteFieldQuarticSymbol_order_four
    (k : Type*) [Field k] [Fintype k]
    (h4 : 4 ∣ Fintype.card k - 1) :
    ∃ u : kˣ,
      orderOf (AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        k (⟨4, by decide⟩ : ℕ+) h4 u) = 4 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  let m := (Fintype.card k - 1) / 4
  have hmPos : 0 < m := by
    have h : 0 < Nat.card kˣ := Nat.card_pos
    have hpos : 0 < Fintype.card k - 1 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h
    exact Nat.div_pos (Nat.le_of_dvd hpos h4) (by decide)
  have horder : orderOf g = Fintype.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, Fintype.card_units]
  have hmDvd : m ∣ orderOf g := by
    rw [horder]
    exact Nat.div_dvd_of_dvd h4
  have hqm : Fintype.card k - 1 = m * 4 := by
    exact (Nat.div_mul_cancel h4).symm
  refine ⟨g, ?_⟩
  calc
    orderOf (AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        k (⟨4, by decide⟩ : ℕ+) h4 g) =
      orderOf (((AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol
        k (⟨4, by decide⟩ : ℕ+) h4 g) : rootsOfUnity 4 k) : kˣ) :=
      (Subgroup.orderOf_coe _).symm
    _ = orderOf (g ^ m) := rfl
    _ = orderOf g / m := orderOf_pow_of_dvd hmPos.ne' hmDvd
    _ = 4 := by
      rw [horder, hqm]
      exact Nat.mul_div_cancel_left 4 hmPos

/-- At every Gaussian prime away from two, some integral numerator has a
quartic prime-ideal symbol of order four. -/
theorem exists_gaussianQuarticPrimeSymbol_order_four
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4) :
    ∃ b : 𝓞 GaussianField, ∃ hb : b ∉ P.asIdeal,
      orderOf (gaussianQuarticPrimeSymbol b P h2 hb) = 4 := by
  classical
  letI : Fintype (𝓞 GaussianField ⧸ P.asIdeal) := Fintype.ofFinite _
  have hmu : (primitiveRoots 4 GaussianField).Nonempty := by
    letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {4} ℚ GaussianField :=
      CyclotomicField.isCyclotomicExtension 4 ℚ
    obtain ⟨ζ, hζ⟩ :=
      IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) ℚ GaussianField
        (Set.mem_singleton 4) (by decide : 4 ≠ 0)
    exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 4)).2 hζ⟩
  have h4 : 4 ∣ Fintype.card (𝓞 GaussianField ⧸ P.asIdeal) - 1 := by
    rw [AlgebraicNumberTheory.PowerResidueSymbols.card_primeIdealResidueField
      GaussianField P]
    exact AlgebraicNumberTheory.PowerResidueSymbols.dvd_absNorm_sub_one_of_primitiveRoots
      GaussianField P (⟨4, by decide⟩ : ℕ+) hmu h2
  obtain ⟨u, hu⟩ :=
    exists_finiteFieldQuarticSymbol_order_four
      (𝓞 GaussianField ⧸ P.asIdeal) h4
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 GaussianField ⧸ P.asIdeal)
  have hbP : b ∉ P.asIdeal := by
    intro hmem
    have hzero : (u : 𝓞 GaussianField ⧸ P.asIdeal) = 0 := by
      rw [← hb]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact (Units.ne_zero u) hzero
  refine ⟨b, hbP, ?_⟩
  have hred := gaussianQuarticPrimeSymbol_reduction b P h2 hbP
  have hunit :
      AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
        GaussianField P b hbP = u := by
    apply Units.ext
    exact hb
  dsimp at hred
  rw [hunit] at hred
  have hredOrder := congrArg orderOf hred
  have horder := (AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReductionEquiv
    GaussianField P (⟨4, by decide⟩ : ℕ+) hmu h2).orderOf_eq
    (gaussianQuarticPrimeSymbol b P h2 hbP)
  exact horder.symm.trans (hredOrder.trans hu)

/-- In particular, the quartic symbol is nontrivial at an admissible
Gaussian prime for a suitable numerator. -/
theorem exists_gaussianQuarticPrimeSymbol_ne_one
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4) :
    ∃ b : 𝓞 GaussianField, ∃ hb : b ∉ P.asIdeal,
      gaussianQuarticPrimeSymbol b P h2 hb ≠ 1 := by
  obtain ⟨b, hb, horder⟩ := exists_gaussianQuarticPrimeSymbol_order_four P h2
  refine ⟨b, hb, ?_⟩
  intro h
  simp [h] at horder

/-- At a fixed prime, the quartic symbol depends only on the numerator's
residue class. -/
theorem gaussianQuarticPrimeSymbol_eq_of_sub_mem
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (b c : 𝓞 GaussianField)
    (hb : b ∉ P.asIdeal) (hc : c ∉ P.asIdeal)
    (hbc : b - c ∈ P.asIdeal) :
    gaussianQuarticPrimeSymbol b P h2 hb =
      gaussianQuarticPrimeSymbol c P h2 hc := by
  classical
  letI : Fintype (𝓞 GaussianField ⧸ P.asIdeal) := Fintype.ofFinite _
  have hunit :
      AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
        GaussianField P b hb =
      AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
        GaussianField P c hc := by
    apply Units.ext
    exact (Submodule.Quotient.eq P.asIdeal).mpr hbc
  have hredB := gaussianQuarticPrimeSymbol_reduction b P h2 hb
  have hredC := gaussianQuarticPrimeSymbol_reduction c P h2 hc
  dsimp at hredB hredC
  rw [hunit] at hredB
  have heq := hredB.trans hredC.symm
  exact (AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReductionEquiv
    GaussianField P (⟨4, by decide⟩ : ℕ+)
    (by
      letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
      letI : IsCyclotomicExtension {4} ℚ GaussianField :=
        CyclotomicField.isCyclotomicExtension 4 ℚ
      obtain ⟨ζ, hζ⟩ :=
        IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) ℚ GaussianField
          (Set.mem_singleton 4) (by decide : 4 ≠ 0)
      exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 4)).2 hζ⟩) h2).injective heq

/-- The unit ideal is admissible for every quartic numerator. -/
theorem gaussianQuarticGoodIdeal_one (b : 𝓞 GaussianField) :
    GaussianQuarticGoodIdeal b 1 := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  have htop : P.asIdeal = ⊤ :=
    top_unique (Ideal.dvd_iff_le.mp (by simpa only [Ideal.one_eq_top] using hP))
  exact (P.isPrime.ne_top htop).elim

/-- The ideal symbol of the unit ideal is one. -/
theorem gaussianQuarticIdealSymbol_one (b : 𝓞 GaussianField) :
    gaussianQuarticIdealSymbol b 1 (gaussianQuarticGoodIdeal_one b) = 1 := by
  haveI : IsEmpty
      (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeDivisors
        GaussianField (1 : Ideal (𝓞 GaussianField))) :=
    ⟨fun P => (P.1.isPrime.ne_top
      (top_unique (Ideal.dvd_iff_le.mp
        (by simpa only [Ideal.one_eq_top] using
          (AlgebraicNumberTheory.PowerResidueSymbols.mem_idealPrimeDivisors
            GaussianField 1 P.1).mp P.2)))).elim⟩
  unfold gaussianQuarticIdealSymbol
    AlgebraicNumberTheory.PowerResidueSymbols.idealPowerResidueSymbol
  simp

/-- Powers of a prime ideal away from `2b` remain admissible. -/
theorem gaussianQuarticGoodIdeal_prime_pow
    (b : 𝓞 GaussianField)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hb : b ∉ P.asIdeal) (e : ℕ) :
    GaussianQuarticGoodIdeal b (P.asIdeal ^ e) := by
  induction e with
  | zero => simpa using gaussianQuarticGoodIdeal_one b
  | succ e ih =>
      simpa only [pow_succ] using
        gaussianQuarticGoodIdeal_mul b (P.asIdeal ^ e) P.asIdeal ih
          (gaussianQuarticGoodIdeal_prime b P h2 hb)

/-- The quartic symbol of a prime-ideal power is the matching power of
the prime symbol. -/
theorem gaussianQuarticIdealSymbol_prime_pow
    (b : 𝓞 GaussianField)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hb : b ∉ P.asIdeal) (e : ℕ) :
    gaussianQuarticIdealSymbol b (P.asIdeal ^ e)
        (gaussianQuarticGoodIdeal_prime_pow b P h2 hb e) =
      gaussianQuarticPrimeSymbol b P h2 hb ^ e := by
  induction e with
  | zero => simpa using gaussianQuarticIdealSymbol_one b
  | succ e ih =>
      have hmul := gaussianQuarticIdealSymbol_mul b
        (P.asIdeal ^ e) P.asIdeal
        (gaussianQuarticGoodIdeal_prime_pow b P h2 hb e)
        (gaussianQuarticGoodIdeal_prime b P h2 hb)
      rw [gaussianQuarticIdealSymbol_prime b P h2 hb] at hmul
      simpa only [pow_succ, ih] using hmul

/-- CRT isolates one prime-power factor of an admissible denominator ideal.
An auxiliary coprime modulus can simultaneously force the numerator to be
congruent to one, as required at the dyadic places in reciprocity. -/
theorem exists_nontrivial_quartic_symbol_of_prime_power_factor_with_congruence
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (J D : Ideal (𝓞 GaussianField)) (e : ℕ)
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hJ0 : J ≠ 0)
    (hJ2 : ∀ Q : HeightOneSpectrum (𝓞 GaussianField),
      Q.asIdeal ∣ J → (Ideal.absNorm Q.asIdeal).Coprime 4)
    (hcop : IsCoprime P.asIdeal J)
    (hPD : IsCoprime P.asIdeal D)
    (hJD : IsCoprime J D)
    (he : ¬ 4 ∣ e) :
    ∃ b : 𝓞 GaussianField,
      b - 1 ∈ D ∧
        ∃ hgood : GaussianQuarticGoodIdeal b (P.asIdeal ^ e * J),
          gaussianQuarticIdealSymbol b (P.asIdeal ^ e * J) hgood ≠ 1 := by
  classical
  obtain ⟨seed, hseedP, hseedOrder⟩ :=
    exists_gaussianQuarticPrimeSymbol_order_four P h2
  let f : Fin 3 → Ideal (𝓞 GaussianField) := ![P.asIdeal, J, D]
  let x : Fin 3 → 𝓞 GaussianField := ![seed, 1, 1]
  have hf : Pairwise (fun i j => IsCoprime (f i) (f j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [f] using hcop
    · simpa [f] using hPD
    · simpa [f] using hcop.symm
    · exact (hij rfl).elim
    · simpa [f] using hJD
    · simpa [f] using hPD.symm
    · simpa [f] using hJD.symm
    · exact (hij rfl).elim
  obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal hf x
  have hbPcong : b - seed ∈ P.asIdeal := by simpa [f, x] using hb 0
  have hbJcong : b - 1 ∈ J := by simpa [f, x] using hb 1
  have hbDcong : b - 1 ∈ D := by simpa [f, x] using hb 2
  have hbP : b ∉ P.asIdeal := by
    intro hbmem
    apply hseedP
    have h := P.asIdeal.sub_mem hbmem hbPcong
    convert h using 1 <;> ring
  have hPgood := gaussianQuarticGoodIdeal_prime_pow b P h2 hbP e
  have hJgood : GaussianQuarticGoodIdeal b J := by
    refine ⟨hJ0, ?_⟩
    intro Q hQ
    refine ⟨hJ2 Q hQ, ?_⟩
    have hbQcong : b - 1 ∈ Q.asIdeal := (Ideal.dvd_iff_le.mp hQ) hbJcong
    intro hbQ
    have hone : (1 : 𝓞 GaussianField) ∈ Q.asIdeal := by
      have h := Q.asIdeal.sub_mem hbQ hbQcong
      convert h using 1 <;> ring
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one Q.asIdeal).mpr hone)
  let hgood := gaussianQuarticGoodIdeal_mul b (P.asIdeal ^ e) J hPgood hJgood
  refine ⟨b, hbDcong, hgood, ?_⟩
  have hPval :
      gaussianQuarticPrimeSymbol b P h2 hbP =
        gaussianQuarticPrimeSymbol seed P h2 hseedP :=
    gaussianQuarticPrimeSymbol_eq_of_sub_mem P h2 b seed hbP hseedP hbPcong
  have hPorder : orderOf (gaussianQuarticPrimeSymbol b P h2 hbP) = 4 := by
    rw [hPval]
    exact hseedOrder
  have hpowNe : gaussianQuarticPrimeSymbol b P h2 hbP ^ e ≠ 1 := by
    intro hpow
    apply he
    rw [← hPorder]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hJone := gaussianQuarticIdealSymbol_eq_one_of_sub_one_mem b J hJgood hbJcong
  have hmul := gaussianQuarticIdealSymbol_mul b (P.asIdeal ^ e) J hPgood hJgood
  rw [gaussianQuarticIdealSymbol_prime_pow b P h2 hbP e, hJone, mul_one] at hmul
  exact fun h => hpowNe (hmul.symm.trans h)

/-- Reciprocity transfers a nonidentity reverse quartic symbol to the
forward symbol when the auxiliary generator is one modulo `64`. -/
theorem gaussianQuarticIdealSymbol_ne_one_of_reverse_and_dyadic_congruence
    (a b : 𝓞 GaussianField) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hBA : GaussianQuarticGoodIdeal b (Ideal.span {a}))
    (h64 : b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)})
    (hBAne : gaussianQuarticIdealSymbol b (Ideal.span {a}) hBA ≠ 1) :
    gaussianQuarticIdealSymbol a (Ideal.span {b})
      (gaussianQuarticGoodIdeal_reciprocal_of_good_and_congruent_sixtyfour
        a b hb0 hBA h64) ≠ 1 := by
  have hrec := gaussianQuarticIdealSymbol_reciprocity_of_local_fourth_powers
    a b ha0 hb0
    (gaussianQuarticGoodIdeal_reciprocal_of_good_and_congruent_sixtyfour
      a b hb0 hBA h64) hBA
    (fun v hv => gaussianDyadic_exists_fourth_root v hv b h64)
  exact hrec.symm ▸ hBAne

/-- A non-fourth-power prime exponent in a factorization of `(a)` yields an
auxiliary principal denominator on which the quartic symbol of `a` is
nontrivial. The auxiliary generator is one modulo rational `64`. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_of_prime_power_factor
    (a : 𝓞 GaussianField) (ha0 : a ≠ 0)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (J : Ideal (𝓞 GaussianField)) (e : ℕ)
    (hfactor : Ideal.span {a} = P.asIdeal ^ e * J)
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (hJ0 : J ≠ 0)
    (hJ2 : ∀ Q : HeightOneSpectrum (𝓞 GaussianField),
      Q.asIdeal ∣ J → (Ideal.absNorm Q.asIdeal).Coprime 4)
    (hcop : IsCoprime P.asIdeal J)
    (hP64 : IsCoprime P.asIdeal
      (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}))
    (hJ64 : IsCoprime J
      (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}))
    (he : ¬ 4 ∣ e) :
    ∃ b : 𝓞 GaussianField,
      b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} ∧
        ∃ hgood : GaussianQuarticGoodIdeal a (Ideal.span {b}),
          gaussianQuarticIdealSymbol a (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨b, h64, hBA, hBAne⟩ :=
    exists_nontrivial_quartic_symbol_of_prime_power_factor_with_congruence
      P J (Ideal.span {((64 : ℕ) : 𝓞 GaussianField)}) e
      h2 hJ0 hJ2 hcop hP64 hJ64 he
  have hb0 := gaussian_ne_zero_of_sub_one_mem_sixtyfour b h64
  have hBA' : GaussianQuarticGoodIdeal b (Ideal.span {a}) := by
    simpa only [hfactor] using hBA
  have hBAne' : gaussianQuarticIdealSymbol b (Ideal.span {a}) hBA' ≠ 1 := by
    simpa only [hfactor] using hBAne
  refine ⟨b, h64,
    gaussianQuarticGoodIdeal_reciprocal_of_good_and_congruent_sixtyfour
      a b hb0 hBA' h64, ?_⟩
  exact gaussianQuarticIdealSymbol_ne_one_of_reverse_and_dyadic_congruence
    a b ha0 hb0 hBA' h64 hBAne'

/-- A signed odd rational radicand with an odd-prime exponent not divisible
by four has a nontrivial Gaussian quartic symbol on a principal ideal. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_of_signed_odd_prime_exponent
    (R s : ℤ) (p e : ℕ) (hR0 : R ≠ 0) (hOdd : Odd R)
    (hp : p.Prime) (hpodd : p ≠ 2)
    (hR : R = (p : ℤ) ^ e * s) (hps : ¬ (p : ℤ) ∣ s)
    (he : ¬ 4 ∣ e) :
    ∃ b : 𝓞 GaussianField,
      b - 1 ∈ Ideal.span {((64 : ℕ) : 𝓞 GaussianField)} ∧
        ∃ hgood : GaussianQuarticGoodIdeal (R : 𝓞 GaussianField)
            (Ideal.span {b}),
          gaussianQuarticIdealSymbol (R : 𝓞 GaussianField)
            (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨P, J, hP2, hJ0, hJ2, hPJ, hP64, hJ64, hfac⟩ :=
    gaussianSignedOddInteger_prime_power_factor R s p e hR0 hOdd hp hpodd hR hps he
  exact exists_nontrivial_gaussianQuarticIdealSymbol_of_prime_power_factor
    (R : 𝓞 GaussianField) (by exact_mod_cast hR0)
    P J e hfac hP2 hJ0 hJ2 hPJ hP64 hJ64 he

/-- At a Gaussian prime of residue-field size `5 mod 8`, the quartic
symbol of `-1` is nontrivial. -/
theorem gaussianQuarticPrimeSymbol_negative_one_ne_one_of_norm_mod_eight
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let hneg : (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
      intro hm
      have hone : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
        simpa using P.asIdeal.neg_mem hm
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
    gaussianQuarticPrimeSymbol (-1) P h2 hneg ≠ 1 := by
  classical
  letI : Fintype (𝓞 GaussianField ⧸ P.asIdeal) := Fintype.ofFinite _
  let k := 𝓞 GaussianField ⧸ P.asIdeal
  have hcard : Fintype.card k = Ideal.absNorm P.asIdeal :=
    AlgebraicNumberTheory.PowerResidueSymbols.card_primeIdealResidueField
      GaussianField P
  have hodd : Odd ((Fintype.card k - 1) / 4) := by
    apply Nat.odd_iff.mpr
    omega
  have hChar : ringChar k ≠ 2 := by
    intro hchar
    have heven := FiniteField.even_card_of_char_two hchar
    omega
  have hminus : (-1 : kˣ) ≠ 1 := by
    intro h
    exact Ring.neg_one_ne_one_of_char_ne_two hChar
      (congrArg (fun u : kˣ => (u : k)) h)
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  have hneg : (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro hm
    have hone : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
      simpa using P.asIdeal.neg_mem hm
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  change gaussianQuarticPrimeSymbol (-1) P h2 hneg ≠ 1
  intro hsymbol
  have hred := gaussianQuarticPrimeSymbol_reduction (-1) P h2 hneg
  rw [hsymbol] at hred
  simp only [map_one] at hred
  have hvalue : (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
      GaussianField P (-1) hneg : kˣ) = -1 := by
    apply Units.ext
    simp [AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit]
  have hpower : ((-1 : kˣ) ^ ((Fintype.card k - 1) / 4)) = 1 := by
    have hh := congrArg (fun z : rootsOfUnity 4 k => (z : kˣ)) hred.symm
    have hh' :
        (AlgebraicNumberTheory.PowerResidueSymbols.primeIdealResidueUnit
          GaussianField P (-1) hneg : kˣ) ^ ((Fintype.card k - 1) / 4) = 1 := by
      change _ ^ _ = 1 at hh
      exact hh
    simpa only [hvalue] using hh'
  rw [hodd.neg_one_pow] at hpower
  exact hminus hpower

/-- A nonpower radicand yields infinitely many primes at which the Frobenius
of its simple Kummer extension is nonidentity. -/
theorem infinite_nonidentity_kummer_frobenius
    (K : Type) [Field K] [NumberField K]
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ)
    (ha : a ∉ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    letI : FiniteDimensional K E :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
    letI : IsAbelianGalois K E :=
      KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
    letI : NumberField E := NumberField.of_module_finite K E
    Set.Infinite
      {P : Ideal (𝓞 K) | P.IsPrime ∧ Chebotarev.UnramifiedIn K E P ∧
        Chebotarev.frobeniusClass K E P ≠ ConjClasses.mk 1} := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  letI : FiniteDimensional K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  letI : IsAbelianGalois K E :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  letI : NumberField E := NumberField.of_module_finite K E
  have haClass : ClassFieldTheory.powerClass K n a ≠ 1 := by
    intro h
    exact ha ((ClassFieldTheory.powerClass_eq_one_iff K n a).mp h)
  have hcardNe : Nat.card Gal(E/K) ≠ 1 := by
    intro h
    have horder : orderOf (ClassFieldTheory.powerClass K n a) = 1 := by
      calc
        orderOf (ClassFieldTheory.powerClass K n a) = Module.finrank K E :=
          (ClassFieldTheory.LocalClassFieldTheory.Kummer.chosenSimpleKummerExtension_finrank_eq_powerClassOrder
            K n hnK hmu a).symm
        _ = Nat.card Gal(E/K) := (IsGalois.card_aut_eq_finrank K E).symm
        _ = 1 := h
    exact haClass (orderOf_eq_one_iff.mp horder)
  have hcard : 1 < Nat.card Gal(E/K) := by
    have hpos : 0 < Nat.card Gal(E/K) := Nat.card_pos
    omega
  letI : Nontrivial Gal(E/K) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(E/K), σ ≠ 1 := exists_ne 1
  have hclass : ConjClasses.mk σ ≠ ConjClasses.mk (1 : Gal(E/K)) := by
    intro h
    apply hσ
    have hc : IsConj σ (1 : Gal(E/K)) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp h
    rcases hc with ⟨c, hc⟩
    change (c : Gal(E/K)) * σ = 1 * (c : Gal(E/K)) at hc
    exact mul_left_cancel (by simpa only [one_mul, mul_one] using hc)
  have hinfinite :=
    Chebotarev.infinite_setOf_frobenius_class (K := K) (L := E)
      (ConjClasses.mk σ)
  apply hinfinite.mono
  intro P hP
  exact ⟨hP.1, hP.2.1, hP.2.2 ▸ hclass⟩

end

end Erdos940.Quartic
