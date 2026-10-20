import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Gaussian integers and the fourth cyclotomic ring

The fourth cyclotomic ring is generated over `ℤ` by a primitive fourth
root of unity.  This file relates that presentation to `GaussianInt`.
-/

namespace Erdos940.Quartic

open scoped NumberField

private abbrev FourthCyclotomicRing := CyclotomicRing 4 ℤ ℚ

private noncomputable def fourthZeta : FourthCyclotomicRing :=
  IsCyclotomicExtension.zeta 4 ℤ FourthCyclotomicRing

private theorem fourthZeta_primitive : IsPrimitiveRoot fourthZeta 4 :=
  IsCyclotomicExtension.zeta_spec 4 ℤ FourthCyclotomicRing

private theorem fourthZeta_sq : fourthZeta * fourthZeta = -1 := by
  have hfour : fourthZeta ^ 4 = 1 := fourthZeta_primitive.pow_eq_one
  have htwo : fourthZeta ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by decide : 2 ≠ 0)
      (by simp [← fourthZeta_primitive.eq_orderOf] : 2 < orderOf fourthZeta)
  have hprod : (fourthZeta ^ 2 - 1) * (fourthZeta ^ 2 + 1) = 0 := by
    calc
      (fourthZeta ^ 2 - 1) * (fourthZeta ^ 2 + 1) = fourthZeta ^ 4 - 1 := by ring
      _ = 0 := by rw [hfour]; ring
  have hzero : fourthZeta ^ 2 + 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr htwo)
  simpa [pow_two] using (eq_neg_of_add_eq_zero_left hzero)

/-- The fourth cyclotomic integer ring, presented by adjoining `i` to `ℤ`. -/
noncomputable def gaussianToFourthCyclotomic : GaussianInt →+* FourthCyclotomicRing :=
  Zsqrtd.lift ⟨fourthZeta, by simpa using fourthZeta_sq⟩

theorem gaussianToFourthCyclotomic_i :
    gaussianToFourthCyclotomic Zsqrtd.sqrtd = fourthZeta := by
  simp [gaussianToFourthCyclotomic]

theorem gaussianToFourthCyclotomic_injective :
    Function.Injective gaussianToFourthCyclotomic := by
  haveI : CharZero FourthCyclotomicRing :=
    charZero_of_injective_algebraMap (CyclotomicRing.algebraBase_injective 4 ℤ ℚ)
  exact Zsqrtd.lift_injective
    ⟨fourthZeta, by simpa using fourthZeta_sq⟩
    (by intro n hn; nlinarith [sq_nonneg (n : ℝ)])

theorem gaussianToFourthCyclotomic_surjective :
    Function.Surjective gaussianToFourthCyclotomic := by
  intro x
  have hx : x ∈ Algebra.adjoin ℤ ({fourthZeta} : Set FourthCyclotomicRing) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top fourthZeta_primitive]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨Zsqrtd.sqrtd, gaussianToFourthCyclotomic_i⟩
  | algebraMap z =>
      exact ⟨(z : GaussianInt), by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨a, rfl⟩ := ihx
      obtain ⟨b, rfl⟩ := ihy
      exact ⟨a + b, map_add _ _ _⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨a, rfl⟩ := ihx
      obtain ⟨b, rfl⟩ := ihy
      exact ⟨a * b, map_mul _ _ _⟩

/-- The Gaussian integers are the ring of integers of the fourth cyclotomic field. -/
noncomputable def gaussianFourthCyclotomicEquiv :
    GaussianInt ≃+* FourthCyclotomicRing :=
  RingEquiv.ofBijective gaussianToFourthCyclotomic
    ⟨gaussianToFourthCyclotomic_injective, gaussianToFourthCyclotomic_surjective⟩

/-- A concrete equivalence with the ring of integers of the fourth cyclotomic field. -/
noncomputable def gaussianFourthIntegerRingEquiv :
    GaussianInt ≃+* 𝓞 (CyclotomicField 4 ℚ) := by
  letI : IsIntegralClosure FourthCyclotomicRing ℤ (CyclotomicField 4 ℚ) :=
    IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure 4
  exact gaussianFourthCyclotomicEquiv.trans
    (IsIntegralClosure.equiv ℤ FourthCyclotomicRing
      (CyclotomicField 4 ℚ) (𝓞 (CyclotomicField 4 ℚ))).toRingEquiv

/-- The complex embedding of the fourth cyclotomic integer ring,
oriented so that its distinguished generator maps to `i`. -/
noncomputable def fourthIntegerRingToComplex :
    𝓞 (CyclotomicField 4 ℚ) →+* ℂ :=
  GaussianInt.toComplex.comp gaussianFourthIntegerRingEquiv.symm.toRingHom

@[simp] theorem fourthIntegerRingToComplex_gaussian (z : GaussianInt) :
    fourthIntegerRingToComplex (gaussianFourthIntegerRingEquiv z) = (z : ℂ) := by
  simp [fourthIntegerRingToComplex]

theorem fourthIntegerRingToComplex_injective :
    Function.Injective fourthIntegerRingToComplex := by
  exact GaussianInt.toComplex_injective.comp gaussianFourthIntegerRingEquiv.symm.injective

theorem gaussian_irreducible_of_prime_norm (π : GaussianInt)
    (hp : π.norm.natAbs.Prime) : Irreducible π := by
  rw [irreducible_iff]
  constructor
  · intro hu
    have hn : π.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
    exact hp.ne_one hn
  · intro a b hab
    have hn : π.norm.natAbs = a.norm.natAbs * b.norm.natAbs := by
      rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rcases Nat.prime_mul_iff.mp (hn ▸ hp) with ⟨_, hb⟩ | ⟨_, ha⟩
    · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp hb)
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)

/-- A nonzero reduction map killing a Gaussian prime has exactly that
prime's multiples as its kernel. -/
theorem gaussian_reduction_zero_iff_dvd
    (F : Type*) [Field F]
    (π : GaussianInt) (hp : π.norm.natAbs.Prime)
    (ρ : GaussianInt →+* F) (hρπ : ρ π = 0) (z : GaussianInt) :
    ρ z = 0 ↔ π ∣ z := by
  constructor
  · intro hz
    by_contra hdiv
    obtain ⟨a, b, hab⟩ :=
      ((gaussian_irreducible_of_prime_norm π hp).coprime_iff_not_dvd.mpr hdiv)
    have h := congrArg ρ hab
    simp [hρπ, hz] at h
  · rintro ⟨w, rfl⟩
    simp [hρπ]

/-- Reduction from Gaussian integers to a rational residue field after
choosing one square root of `-1` in that field. -/
def gaussianReduction (q : ℕ) (t : ZMod q) (ht : t * t = -1) :
    GaussianInt →+* ZMod q :=
  Zsqrtd.lift ⟨t, by simpa using ht⟩

@[simp] theorem gaussianReduction_apply (q : ℕ) (t : ZMod q)
    (ht : t * t = -1) (z : GaussianInt) :
    gaussianReduction q t ht z = (z.re : ZMod q) + (z.im : ZMod q) * t :=
  rfl

theorem gaussianReduction_zero_iff_dvd
    (q : ℕ) [Fact q.Prime] (t : ZMod q) (ht : t * t = -1)
    (π : GaussianInt) (hπ : π.norm.natAbs = q)
    (hπt : (π.re : ZMod q) + (π.im : ZMod q) * t = 0)
    (z : GaussianInt) :
    gaussianReduction q t ht z = 0 ↔ π ∣ z := by
  apply gaussian_reduction_zero_iff_dvd (ZMod q) π
  · simpa [hπ] using (Fact.out : q.Prime)
  · simpa using hπt

/-- Of the two orientations of a square root of `-1` modulo the norm,
one annihilates the specified Gaussian prime. -/
theorem gaussianReduction_or_conjugate_kills
    (q : ℕ) [Fact q.Prime] (π : GaussianInt)
    (hπ : π.norm.natAbs = q) (t : ZMod q) (ht : t * t = -1) :
    (π.re : ZMod q) + (π.im : ZMod q) * t = 0 ∨
      (π.re : ZMod q) + (π.im : ZMod q) * (-t) = 0 := by
  have hn : (π.norm : ZMod q) = 0 := by
    rw [← GaussianInt.abs_natCast_norm, hπ]
    simp
  have hprod :
      ((π.re : ZMod q) + (π.im : ZMod q) * t) *
        ((π.re : ZMod q) - (π.im : ZMod q) * t) = 0 := by
    calc
      _ = (π.re : ZMod q) * (π.re : ZMod q) -
            (π.im : ZMod q) * (π.im : ZMod q) * (t * t) := by ring
      _ = (π.norm : ZMod q) := by
        rw [ht]
        simp [Zsqrtd.norm]
      _ = 0 := hn
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [sub_eq_add_neg] using h)

theorem prime_gaussian_norm_mod_four_ne_three
    (q : ℕ) (π : GaussianInt) (hπ : π.norm.natAbs = q) :
    q % 4 ≠ 3 := by
  have hcast : π.norm = (q : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hπ
    rwa [GaussianInt.abs_natCast_norm] at h
  have hn : (q : ℤ) = π.re ^ 2 + π.im ^ 2 := by
    simpa [Zsqrtd.norm, pow_two] using hcast.symm
  have hqmod : (q : ℤ) % 4 = (π.re % 2 + π.im % 2) % 4 := by
    rw [hn, Int.add_emod, Int.sq_emod_four, Int.sq_emod_four]
  omega

/-- Every Gaussian prime of rational prime norm determines a reduction to
the corresponding finite field. -/
theorem exists_gaussian_reduction_at_prime
    (q : ℕ) [Fact q.Prime] (π : GaussianInt)
    (hπ : π.norm.natAbs = q) :
    ∃ (t : ZMod q) (ht : t * t = -1), gaussianReduction q t ht π = 0 := by
  obtain ⟨t, ht⟩ : IsSquare (-1 : ZMod q) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr
      (prime_gaussian_norm_mod_four_ne_three q π hπ)
  rcases gaussianReduction_or_conjugate_kills q π hπ t ht.symm with h | h
  · exact ⟨t, ht.symm, h⟩
  · have hneg : (-t) * (-t) = (-1 : ZMod q) := by simpa using ht.symm
    exact ⟨-t, hneg, h⟩

/-- Concrete finite-field reduction with principal Gaussian-prime kernel. -/
theorem exists_gaussian_reduction_with_kernel
    (q : ℕ) [Fact q.Prime] (π : GaussianInt)
    (hπ : π.norm.natAbs = q) :
    ∃ ρ : GaussianInt →+* ZMod q, ∀ z, ρ z = 0 ↔ π ∣ z := by
  obtain ⟨t, ht, hπt⟩ := exists_gaussian_reduction_at_prime q π hπ
  exact ⟨gaussianReduction q t ht,
    fun z => gaussianReduction_zero_iff_dvd q t ht π hπ
      (by simpa using hπt) z⟩

end Erdos940.Quartic
