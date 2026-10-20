import Erdos940.Quartic.GaussianKummerNontrivial
import Erdos940.Quartic.JacobiTraceBridge
import Erdos940.Quartic.GaussianTwoCharacter
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumTwoSquares

/-!
# The dyadic nontriviality case for Gaussian quartic characters

When the rational radicand is the negative of a fourth power, odd-prime
valuations cannot detect its Kummer class. A split Gaussian prime of norm
`5 mod 8` does: the quartic character of `-1` is nontrivial there. Dirichlet's
theorem lets us choose such a prime away from the fourth-power factor.
-/

namespace Erdos940.Quartic

open scoped BigOperators
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols

def dyadicQuarticLevel : ℕ+ := ⟨4, by decide⟩

attribute [local instance] Ideal.Quotient.field

theorem dyadicPrimitiveFourthRoots :
    (primitiveRoots 4 GaussianField).Nonempty := by
  letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {4}) ℚ GaussianField
      (Set.mem_singleton 4) (by decide : 4 ≠ 0)
  exact ⟨ζ, (mem_primitiveRoots (by decide : 0 < 4)).2 hζ⟩

/-- A split prime of norm `5 mod 8`, chosen above the size of a rational
integer that must be avoided. -/
private theorem exists_large_gaussian_prime_mod_eight (u : ℤ) :
    ∃ (q : ℕ) (π : GaussianInt),
      q.Prime ∧ u.natAbs < q ∧ q % 8 = 5 ∧ π.norm.natAbs = q := by
  obtain ⟨q, hqgt, hqprime, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq u.natAbs (q := 8) (a := 5)
      (by decide) (by decide)
  have hq8 : q % 8 = 5 := by
    simpa [Nat.ModEq] using hqmod
  letI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := q) (by omega)
  let π : GaussianInt := ⟨a, b⟩
  refine ⟨q, π, hqprime, hqgt, hq8, ?_⟩
  have hnorm : π.norm = q := by
    simpa [π, Zsqrtd.norm, sq] using
      congrArg (fun n : ℕ => (n : ℤ)) hab
  simpa [hnorm]

/-- A Gaussian prime above a rational prime `5 mod 8`, avoiding a given
nonzero rational integer. Its defining ideal is principal. -/
theorem exists_gaussian_prime_avoiding_integer_mod_eight
    (u : ℤ) (hu : u ≠ 0) :
    ∃ (P : HeightOneSpectrum (𝓞 GaussianField)) (π : GaussianInt),
      Ideal.absNorm P.asIdeal % 8 = 5 ∧
      (u : 𝓞 GaussianField) ∉ P.asIdeal ∧
      P.asIdeal = Ideal.span {gaussianFourthIntegerRingEquiv π} := by
  obtain ⟨q, π, hqprime, hqgt, hq8, hπnorm⟩ :=
    exists_large_gaussian_prime_mod_eight u
  letI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨ρ, hρker⟩ := exists_gaussian_reduction_with_kernel q π hπnorm
  have hπ0 : π ≠ 0 := by
    intro hzero
    have hq0 : q = 0 := by simpa [hzero] using hπnorm.symm
    exact hqprime.ne_zero hq0
  have hρπ : ρ π = 0 := (hρker π).2 (dvd_refl π)
  let P := gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ
  have hρu : ρ (u : GaussianInt) ≠ 0 := by
    intro hzero
    have hqdiv : (q : ℤ) ∣ u := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd u q).mp
      simpa using hzero
    exact (not_lt_of_ge (Int.natAbs_le_of_dvd_ne_zero hqdiv hu)) hqgt
  refine ⟨P, π, ?_, ?_, ?_⟩
  · simpa [P, gaussianPrimeIdealOfReduction_absNorm] using hq8
  · simpa [P] using gaussianPrimeIdealOfReduction_not_mem q ρ π hπ0 hρπ
      (u : GaussianInt) hρu
  · exact gaussianPrimeIdealOfReduction_eq_span q ρ π hπ0 hρπ hρker

/-- A fourth power has trivial quartic symbol at every admissible prime. -/
theorem gaussianQuarticPrimeSymbol_fourth_power_eq_one
    (a : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4)
    (ha : a ∉ P.asIdeal) :
    gaussianQuarticPrimeSymbol (a ^ 4) P h2
      (fun h => ha (P.isPrime.mem_of_pow_mem 4 h)) = 1 := by
  classical
  letI : Fintype (𝓞 GaussianField ⧸ P.asIdeal) := Fintype.ofFinite _
  let hapow : a ^ 4 ∉ P.asIdeal :=
    fun h => ha (P.isPrime.mem_of_pow_mem 4 h)
  have hred := gaussianQuarticPrimeSymbol_reduction (a ^ 4) P h2 hapow
  have hunit : primeIdealResidueUnit GaussianField P (a ^ 4) hapow =
      (primeIdealResidueUnit GaussianField P a ha) ^ 4 := by
    apply Units.ext
    rfl
  have hn : 4 ∣ Fintype.card (𝓞 GaussianField ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField GaussianField P]
    exact dvd_absNorm_sub_one_of_primitiveRoots GaussianField P
      dyadicQuarticLevel dyadicPrimitiveFourthRoots h2
  have hfinite : finiteFieldPowerResidueSymbol
      (𝓞 GaussianField ⧸ P.asIdeal) dyadicQuarticLevel hn
      (primeIdealResidueUnit GaussianField P (a ^ 4) hapow) = 1 := by
    apply (finiteFieldPowerResidueSymbol_eq_one_iff _ _ _ _).2
    exact ⟨primeIdealResidueUnit GaussianField P a ha, hunit.symm⟩
  have hred0 : (rootsOfUnityReductionEquiv GaussianField P
      dyadicQuarticLevel dyadicPrimitiveFourthRoots h2)
      (gaussianQuarticPrimeSymbol (a ^ 4) P h2 hapow) =
      finiteFieldPowerResidueSymbol
        (𝓞 GaussianField ⧸ P.asIdeal) dyadicQuarticLevel hn
        (primeIdealResidueUnit GaussianField P (a ^ 4) hapow) := by
    exact hred
  rw [hfinite] at hred0
  have hred' : (rootsOfUnityReductionEquiv GaussianField P
      dyadicQuarticLevel dyadicPrimitiveFourthRoots h2)
      (gaussianQuarticPrimeSymbol (a ^ 4) P h2 hapow) = 1 := by
    exact hred0
  have hone : (rootsOfUnityReductionEquiv GaussianField P
      dyadicQuarticLevel dyadicPrimitiveFourthRoots h2)
      (1 : rootsOfUnity 4 (𝓞 GaussianField)) = 1 := map_one _
  exact (rootsOfUnityReductionEquiv GaussianField P dyadicQuarticLevel
    dyadicPrimitiveFourthRoots h2).injective (hred'.trans hone.symm)

/-- The dyadic character remains nontrivial after multiplication by an
unramified rational fourth power. -/
theorem gaussianQuarticPrimeSymbol_negative_fourth_power_ne_one
    (a : 𝓞 GaussianField) (P : HeightOneSpectrum (𝓞 GaussianField))
    (hmod : Ideal.absNorm P.asIdeal % 8 = 5)
    (ha : a ∉ P.asIdeal) :
    let h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
      apply Nat.coprime_of_mul_modEq_one 1
      change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
      omega
    let hR : -(a ^ 4) ∉ P.asIdeal := by
      intro h
      exact ha (P.isPrime.mem_of_pow_mem 4 (by simpa using P.asIdeal.neg_mem h))
    gaussianQuarticPrimeSymbol (-(a ^ 4)) P h2 hR ≠ 1 := by
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  have hneg : (-1 : 𝓞 GaussianField) ∉ P.asIdeal := by
    intro hm
    have hone : (1 : 𝓞 GaussianField) ∈ P.asIdeal := by
      simpa using P.asIdeal.neg_mem hm
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
  have hpow : a ^ 4 ∉ P.asIdeal :=
    fun h => ha (P.isPrime.mem_of_pow_mem 4 h)
  have hR : -(a ^ 4) ∉ P.asIdeal := by
    intro h
    exact hpow (by simpa using P.asIdeal.neg_mem h)
  have hmul : gaussianQuarticPrimeSymbol (-(a ^ 4)) P h2 hR =
      gaussianQuarticPrimeSymbol (-1) P h2 hneg *
        gaussianQuarticPrimeSymbol (a ^ 4) P h2 hpow := by
    have hm := gaussianQuarticIdealSymbol_mul_numerator (-1) (a ^ 4)
      P.asIdeal
      (gaussianQuarticGoodIdeal_prime (-1) P h2 hneg)
      (gaussianQuarticGoodIdeal_prime (a ^ 4) P h2 hpow)
    simp only [neg_one_mul] at hm
    change gaussianQuarticIdealSymbol (-(a ^ 4)) P.asIdeal
        (gaussianQuarticGoodIdeal_prime (-(a ^ 4)) P h2 hR) =
      gaussianQuarticIdealSymbol (-1) P.asIdeal
        (gaussianQuarticGoodIdeal_prime (-1) P h2 hneg) *
      gaussianQuarticIdealSymbol (a ^ 4) P.asIdeal
        (gaussianQuarticGoodIdeal_prime (a ^ 4) P h2 hpow) at hm
    rw [gaussianQuarticIdealSymbol_prime (-(a ^ 4)) P h2 hR,
      gaussianQuarticIdealSymbol_prime (-1) P h2 hneg,
      gaussianQuarticIdealSymbol_prime (a ^ 4) P h2 hpow] at hm
    exact hm
  have hneg_ne : gaussianQuarticPrimeSymbol (-1) P h2 hneg ≠ 1 :=
    gaussianQuarticPrimeSymbol_negative_one_ne_one_of_norm_mod_eight P hmod
  change gaussianQuarticPrimeSymbol (-(a ^ 4)) P h2 hR ≠ 1
  rw [hmul, gaussianQuarticPrimeSymbol_fourth_power_eq_one a P h2 ha, mul_one]
  exact hneg_ne

/-- The Gaussian quartic character for a negative rational fourth power
is nonprincipal. This supplies the dyadic case not detected by odd-prime
valuations. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_negative_fourth_power
    (u : ℤ) (hu : u ≠ 0) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal ((-(u ^ 4) : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol ((-(u ^ 4) : ℤ) : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1 := by
  obtain ⟨P, π, hmod, huP, hspan⟩ :=
    exists_gaussian_prime_avoiding_integer_mod_eight u hu
  have h2 : (Ideal.absNorm P.asIdeal).Coprime 4 := by
    apply Nat.coprime_of_mul_modEq_one 1
    change (Ideal.absNorm P.asIdeal * 1) % 4 = 1 % 4
    omega
  have hR : -((u : 𝓞 GaussianField) ^ 4) ∉ P.asIdeal := by
    intro h
    exact huP (P.isPrime.mem_of_pow_mem 4 (by simpa using P.asIdeal.neg_mem h))
  have hcast : ((-(u ^ 4) : ℤ) : 𝓞 GaussianField) =
      -((u : 𝓞 GaussianField) ^ 4) := by push_cast; rfl
  let b : 𝓞 GaussianField := gaussianFourthIntegerRingEquiv π
  have hgood : GaussianQuarticGoodIdeal ((-(u ^ 4) : ℤ) : 𝓞 GaussianField)
      (Ideal.span {b}) := by
    rw [hcast, ← hspan]
    exact gaussianQuarticGoodIdeal_prime _ P h2 hR
  refine ⟨b, hgood, ?_⟩
  have hprime := gaussianQuarticPrimeSymbol_negative_fourth_power_ne_one
    (u : 𝓞 GaussianField) P hmod huP
  have hprime' : gaussianQuarticPrimeSymbol
      (-((u : 𝓞 GaussianField) ^ 4)) P h2 hR ≠ 1 := hprime
  have hprimeIdeal : gaussianQuarticIdealSymbol
      (-((u : 𝓞 GaussianField) ^ 4)) P.asIdeal
      (gaussianQuarticGoodIdeal_prime _ P h2 hR) ≠ 1 := by
    rw [gaussianQuarticIdealSymbol_prime]
    exact hprime'
  simpa only [hcast, hspan] using hprimeIdeal

end Erdos940.Quartic
