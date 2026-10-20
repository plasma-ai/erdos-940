import Erdos940.Quartic.GaussianCharacters
import Erdos940.Quartic.GaussianRingEquivalence
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The quartic Jacobi sum at a Gaussian prime

This file isolates the reduction argument behind the evaluation of the
quartic Jacobi sum.  Reduction modulo a prime of norm `q` sends the quartic
character to the `(q-1)/4`-th power map.  Its Jacobi sum therefore vanishes
modulo that prime: the corresponding polynomial has degree at most `(q-1)/2`.
-/

namespace Erdos940.Quartic

open Finset

private theorem finiteField_sum_pow_mul_one_sub_pow_zero
    (F : Type*) [Field F] [Fintype F] (k : ℕ)
    (hk : 2 * k < Fintype.card F - 1) :
    ∑ x : F, x ^ k * (1 - x) ^ k = 0 := by
  classical
  have hexp (j : ℕ) (hj : j ≤ k) : k + (k - j) < Fintype.card F - 1 := by
    omega
  calc
    (∑ x : F, x ^ k * (1 - x) ^ k) =
        ∑ x : F, ∑ j ∈ Finset.range (k + 1),
          x ^ k * (1 ^ j * (-x) ^ (k - j) * (k.choose j : F)) := by
          apply Fintype.sum_congr
          intro x
          rw [sub_eq_add_neg, add_pow, mul_sum]
    _ = ∑ j ∈ Finset.range (k + 1),
          ∑ x : F, x ^ k * (1 ^ j * (-x) ^ (k - j) * (k.choose j : F)) :=
      Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hpow := FiniteField.sum_pow_lt_card_sub_one F (k + (k - j)) (hexp j hjk)
      calc
        (∑ x : F, x ^ k * (1 ^ j * (-x) ^ (k - j) * (k.choose j : F))) =
            ((k.choose j : F) * (-1) ^ (k - j)) *
              ∑ x : F, x ^ (k + (k - j)) := by
          rw [Finset.mul_sum]
          apply Fintype.sum_congr
          intro x
          simp only [one_pow, one_mul, pow_add]
          ring
        _ = 0 := by rw [hpow, mul_zero]

/-- A Gaussian-integer-valued quartic character whose reduction is the
`k`-th power character has a Jacobi sum in the kernel of reduction. -/
theorem gaussian_jacobi_reduction_zero
    (F : Type*) [Field F] [Fintype F]
    (ρ : GaussianInt →+* F) (γ : F → GaussianInt) (k : ℕ)
    (hk : 2 * k < Fintype.card F - 1)
    (hγ : ∀ x : F, ρ (γ x) = x ^ k) :
    ρ (∑ x : F, γ x * γ (1 - x)) = 0 := by
  classical
  rw [map_sum]
  simp_rw [map_mul, hγ]
  exact finiteField_sum_pow_mul_one_sub_pow_zero F k hk

/-- In `ℤ[i]`, divisibility between elements with the same positive norm
is association.  This is the algebraic step in identifying a Jacobi sum
with the Gaussian prime above the rational prime. -/
theorem gaussian_associated_of_dvd_of_equal_norm
    (π J : GaussianInt) (hπ : 0 < π.norm)
    (hdiv : π ∣ J) (hnorm : J.norm = π.norm) :
    ∃ u : GaussianInt, IsUnit u ∧ J = π * u := by
  obtain ⟨u, hu⟩ := hdiv
  refine ⟨u, ?_, hu⟩
  have hnormu : u.norm = 1 := by
    rw [hu, Zsqrtd.norm_mul] at hnorm
    nlinarith
  exact (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mp hnormu

/-- The Gaussian lift of an order-four Jacobi sum has norm `q`. -/
theorem quartic_jacobi_gaussian_norm
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (J : GaussianInt)
    (hJ : (J : ℂ) = jacobiSum χ χ) :
    J.norm = q := by
  have hnorm := GaussianInt.intCast_complex_norm J
  rw [hJ, Complex.normSq_eq_conj_mul_self] at hnorm
  have hconj := quartic_jacobi_conj q χ hχ
  have hprod := quartic_jacobi_mul_inverse_jacobi q χ hχ
  rw [← hconj] at hprod
  have hq : (J.norm : ℂ) = q := by
    rw [hnorm]
    simpa [mul_comm] using hprod
  exact_mod_cast hq

/-- Every order-four complex character of a prime field has a
Gaussian-integer-valued lift. The lift is pointwise and maps zero to zero. -/
theorem quartic_character_exists_gaussian_lift
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    ∃ γ : ZMod q → GaussianInt,
      ∀ x : ZMod q, (γ x : ℂ) = χ x := by
  classical
  have hχpow : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hpoint (x : ZMod q) : ∃ g : GaussianInt, (g : ℂ) = χ x := by
    by_cases hx : x = 0
    · subst x
      exact ⟨0, by simp [MulChar.map_zero]⟩
    · have hχx4 : (χ x) ^ 4 = 1 := by
        have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ x) hχpow
        simpa [MulChar.pow_apply' χ (by decide : 4 ≠ 0),
          MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)] using hv
      obtain ⟨j, hjlt, hj⟩ := Complex.isPrimitiveRoot_I.eq_pow_of_pow_eq_one hχx4
      refine ⟨(⟨0, 1⟩ : GaussianInt) ^ j, ?_⟩
      rw [map_pow]
      simpa [GaussianInt.toComplex_def] using hj
  exact ⟨fun x => Classical.choose (hpoint x),
    fun x => Classical.choose_spec (hpoint x)⟩

/-- The unique Gaussian-integer-valued lift of a complex quartic
character. The choice is extensional because `GaussianInt.toComplex` is
injective. -/
noncomputable def quarticGaussianLift
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) : ZMod q → GaussianInt :=
  Classical.choose (quartic_character_exists_gaussian_lift q χ hχ)

@[simp]
theorem quarticGaussianLift_complex
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (x : ZMod q) :
    ((quarticGaussianLift q χ hχ x : GaussianInt) : ℂ) = χ x :=
  Classical.choose_spec (quartic_character_exists_gaussian_lift q χ hχ) x

@[simp]
theorem quarticGaussianLift_zero
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    quarticGaussianLift q χ hχ 0 = 0 := by
  apply GaussianInt.toComplex_injective
  simp [MulChar.map_zero]

@[simp]
theorem quarticGaussianLift_one
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    quarticGaussianLift q χ hχ 1 = 1 := by
  apply GaussianInt.toComplex_injective
  simp

theorem quarticGaussianLift_mul
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (x y : ZMod q) :
    quarticGaussianLift q χ hχ (x * y) =
      quarticGaussianLift q χ hχ x * quarticGaussianLift q χ hχ y := by
  apply GaussianInt.toComplex_injective
  simp [map_mul]

/-- The Gaussian lift is a multiplicative map, including zero. -/
noncomputable def quarticGaussianLiftHom
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) : ZMod q →* GaussianInt where
  toFun := quarticGaussianLift q χ hχ
  map_one' := quarticGaussianLift_one q χ hχ
  map_mul' := quarticGaussianLift_mul q χ hχ

/-- Once the quartic complex character is identified with a
Gaussian-integer-valued character whose reduction is the fourth-power
symbol, its Jacobi sum generates the Gaussian prime above `q`, up to a
Gaussian unit.  The character/reduction compatibility is kept explicit so
that it can be established from the selected prime and residue map. -/
theorem quartic_jacobi_gaussian_generator_of_reduction
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (ρ : GaussianInt →+* ZMod q)
    (hρkernel : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (γ : ZMod q → GaussianInt)
    (hγcomplex : ∀ x : ZMod q, (γ x : ℂ) = χ x)
    (hγreduction : ∀ x : ZMod q, ρ (γ x) = x ^ ((q - 1) / 4)) :
    ∃ J u : GaussianInt,
      (J : ℂ) = jacobiSum χ χ ∧ IsUnit u ∧ J = π * u := by
  classical
  let J : GaussianInt := ∑ x : ZMod q, γ x * γ (1 - x)
  have hJcomplex : (J : ℂ) = jacobiSum χ χ := by
    simp only [J, jacobiSum, map_sum, map_mul, hγcomplex]
  have hqprime : q.Prime := Fact.out
  have hqpos : 0 < q := hqprime.pos
  have hq5 : 5 ≤ q := by
    have hq2 := hqprime.two_le
    omega
  have hsize : 2 * ((q - 1) / 4) < Fintype.card (ZMod q) - 1 := by
    rw [ZMod.card]
    omega
  have hρJ : ρ J = 0 := by
    exact gaussian_jacobi_reduction_zero (ZMod q) ρ γ ((q - 1) / 4)
      hsize hγreduction
  have hπpos : 0 < π.norm := by rw [hπnorm]; exact_mod_cast hqpos
  have hnormJ : J.norm = π.norm := by
    rw [hπnorm]
    exact quartic_jacobi_gaussian_norm q χ hχ J hJcomplex
  obtain ⟨u, hu, hJu⟩ := gaussian_associated_of_dvd_of_equal_norm π J
    hπpos ((hρkernel J).mp hρJ) hnormJ
  exact ⟨J, u, hJcomplex, hu, hJu⟩

/-- A symmetric finite sum in characteristic two consists only of its
fixed-point contribution under the involution `x ↦ 1-x`. -/
private theorem symmetric_sum_mod_two
    (F R : Type*) [Field F] [Fintype F] [CommRing R] [CharP R 2]
    (h2 : (2 : F) ≠ 0) (f : F → R)
    (hf : ∀ x, f (1 - x) = f x) :
    ∑ x : F, f x = f (1 / 2 : F) := by
  classical
  let a : F := 1 / 2
  have ha : 1 - a = a := by
    dsimp [a]
    field_simp
    ring
  have hfix (x : F) : 1 - x = x → x = a := by
    intro hx
    have hx2 : (2 : F) * x = 1 := by
      calc
        (2 : F) * x = x + x := by ring
        _ = 1 := by linear_combination -hx
    apply (mul_left_cancel₀ h2)
    rw [hx2]
    dsimp [a]
    field_simp
  let s : Finset F := Finset.univ.erase a
  have hsum : (∑ x ∈ s, f x) = 0 := by
    apply Finset.sum_involution (fun x _ => 1 - x)
    · intro x _
      rw [hf]
      have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
      calc
        f x + f x = (2 : R) * f x := by ring
        _ = 0 := by rw [htwo, zero_mul]
    · intro x hx _
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      exact fun heq => hxa (hfix x heq)
    · intro x _
      ring
    · intro x hx
      have hxa : x ≠ a := Finset.ne_of_mem_erase hx
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq
      apply hxa
      have := congrArg (fun z : F => 1 - z) heq
      simpa [ha] using this
  have hdecomp := Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
  calc
    ∑ x : F, f x = f a + ∑ x ∈ s, f x := hdecomp.symm
    _ = f (1 / 2 : F) := by rw [hsum]; simp [a]

private def gaussianRealModTwo : GaussianInt →+ ZMod 2 where
  toFun z := z.re
  map_zero' := by simp
  map_add' x y := by simp [Zsqrtd.re_add]

private def gaussianImagModTwo : GaussianInt →+ ZMod 2 where
  toFun z := z.im
  map_zero' := by simp
  map_add' x y := by simp [Zsqrtd.im_add]

/-- The parity of a symmetric Gaussian-integer sum is entirely the parity
of its term at `1/2`. -/
theorem gaussian_symmetric_sum_parity
    (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (f : F → GaussianInt) (hf : ∀ x, f (1 - x) = f x) :
    (((∑ x : F, f x).re : ℤ) : ZMod 2) =
        ((f (1 / 2 : F)).re : ZMod 2) ∧
      (((∑ x : F, f x).im : ℤ) : ZMod 2) =
        ((f (1 / 2 : F)).im : ZMod 2) := by
  constructor
  · have h := symmetric_sum_mod_two F (ZMod 2) h2
      (fun x => gaussianRealModTwo (f x))
      (fun x => by rw [hf])
    change gaussianRealModTwo (∑ x : F, f x) =
      gaussianRealModTwo (f (1 / 2 : F))
    simpa only [map_sum] using h
  · have h := symmetric_sum_mod_two F (ZMod 2) h2
      (fun x => gaussianImagModTwo (f x))
      (fun x => by rw [hf])
    change gaussianImagModTwo (∑ x : F, f x) =
      gaussianImagModTwo (f (1 / 2 : F))
    simpa only [map_sum] using h

/-- The square of any Gaussian unit is congruent to `1` coefficientwise
modulo `2`. -/
theorem gaussian_unit_square_mod_two
    (u : GaussianInt) (hu : IsUnit u) :
    (((u ^ 2).re : ℤ) : ZMod 2) = 1 ∧
      (((u ^ 2).im : ℤ) : ZMod 2) = 0 := by
  have hnorm : u.re * u.re + u.im * u.im = 1 := by
    have h := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mpr hu
    simpa [Zsqrtd.norm] using h
  have hcast := congrArg (fun z : ℤ => (z : ZMod 2)) hnorm
  constructor
  · calc
      (((u ^ 2).re : ℤ) : ZMod 2) =
          (u.re : ZMod 2) * (u.re : ZMod 2) -
            (u.im : ZMod 2) * (u.im : ZMod 2) := by
        simp only [pow_two, Zsqrtd.re_mul, Int.cast_add, Int.cast_mul,
          Int.cast_neg, Int.cast_one]
        ring
      _ = (u.re : ZMod 2) * (u.re : ZMod 2) +
            (u.im : ZMod 2) * (u.im : ZMod 2) := by
        rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      _ = 1 := by simpa using hcast
  · have htwo : (2 : ZMod 2) = 0 := by decide
    simp only [pow_two, Zsqrtd.im_mul, Int.cast_add, Int.cast_mul]
    calc
      (u.re : ZMod 2) * (u.im : ZMod 2) +
          (u.im : ZMod 2) * (u.re : ZMod 2) =
          (2 : ZMod 2) * (u.re : ZMod 2) * (u.im : ZMod 2) := by ring
      _ = 0 := by rw [htwo]; ring

/-- A Gaussian-valued lift of a quartic character has a Jacobi sum with
odd real part and even imaginary part.  This is the parity normalization
used to reduce the Gaussian-unit ambiguity to a sign. -/
theorem quartic_jacobi_parity_of_gaussian_lift
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (γ : ZMod q → GaussianInt)
    (hγcomplex : ∀ x : ZMod q, (γ x : ℂ) = χ x) :
    (((∑ x : ZMod q, γ x * γ (1 - x)).re : ℤ) : ZMod 2) = 1 ∧
      (((∑ x : ZMod q, γ x * γ (1 - x)).im : ℤ) : ZMod 2) = 0 := by
  classical
  have hqprime : q.Prime := Fact.out
  have hq5 : 5 ≤ q := by
    have hq2 := hqprime.two_le
    omega
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    have hqle2 := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  let a : ZMod q := 1 / 2
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact one_div_ne_zero h2
  have hγ4 : (γ a) ^ 4 = 1 := by
    have hχpow : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hχa4 : (χ a) ^ 4 = 1 := by
      have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ a) hχpow
      simpa [MulChar.pow_apply' χ (by decide : 4 ≠ 0),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr ha0)] using hv
    apply GaussianInt.toComplex_injective
    simpa [hγcomplex] using hχa4
  have hγunit : IsUnit (γ a) := IsUnit.of_pow_eq_one hγ4 (by decide)
  have hfixed := gaussian_unit_square_mod_two (γ a) hγunit
  let f : ZMod q → GaussianInt := fun x => γ x * γ (1 - x)
  have hf : ∀ x, f (1 - x) = f x := by
    intro x
    dsimp [f]
    have hxx : 1 - (1 - x) = x := by ring
    rw [hxx]
    ring
  have hparity := gaussian_symmetric_sum_parity (ZMod q) h2 f hf
  have haf : f a = (γ a) ^ 2 := by
    dsimp [f, a]
    have ha : (1 - (1 / 2 : ZMod q)) = 1 / 2 := by
      field_simp
      ring
    rw [ha, pow_two]
  have hpre : (((∑ x : ZMod q, f x).re : ℤ) : ZMod 2) =
      (((γ a) ^ 2).re : ZMod 2) := by
    convert hparity.1 using 1
    rw [haf]
  have hpim : (((∑ x : ZMod q, f x).im : ℤ) : ZMod 2) =
      (((γ a) ^ 2).im : ZMod 2) := by
    convert hparity.2 using 1
    rw [haf]
  exact ⟨hpre.trans hfixed.1, hpim.trans hfixed.2⟩

/-- Among Gaussian units, the ones with even imaginary coordinate are
exactly the two signs. -/
theorem gaussian_unit_eq_sign_of_im_even
    (u : GaussianInt) (hu : IsUnit u)
    (him : (u.im : ZMod 2) = 0) : u = 1 ∨ u = -1 := by
  have hnorm : u.re * u.re + u.im * u.im = 1 := by
    have h := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mpr hu
    simpa [Zsqrtd.norm] using h
  obtain ⟨t, ht⟩ := ZMod.intCast_eq_zero_iff_even.mp him
  have ht0 : t = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have htle : t ≤ -1 := by omega
      nlinarith [sq_nonneg (u.re), sq_nonneg (t + 1)]
    · have htge : 1 ≤ t := by omega
      nlinarith [sq_nonneg (u.re), sq_nonneg (t - 1)]
  have huim : u.im = 0 := by simpa [ht0] using ht
  have hure : u.re = 1 ∨ u.re = -1 := by
    have hreSq : u.re * u.re = 1 := by simpa [huim] using hnorm
    exact mul_self_eq_one_iff.mp hreSq
  rcases hure with hre | hre
  · left
    apply Zsqrtd.ext <;> simp [hre, huim]
  · right
    apply Zsqrtd.ext <;> simp [hre, huim]

/-- Parity rules out the two imaginary Gaussian units in an association. -/
theorem gaussian_associated_eq_sign_of_parity
    (π J u : GaussianInt) (hu : IsUnit u) (hJ : J = π * u)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (hJim : (J.im : ZMod 2) = 0) :
    J = π ∨ J = -π := by
  have huim : (u.im : ZMod 2) = 0 := by
    have h := congrArg (fun z : GaussianInt => (z.im : ZMod 2)) hJ
    simp only [Zsqrtd.im_mul, Int.cast_add, Int.cast_mul] at h
    rw [hJim, hπre, hπim] at h
    simpa using h.symm
  rcases gaussian_unit_eq_sign_of_im_even u hu huim with rfl | rfl
  · left
    simpa using hJ
  · right
    simpa using hJ

/-- With an odd-real, even-imaginary generator `π`, the Jacobi square is
exactly `π²` once the residue character is identified. -/
theorem quartic_jacobi_square_of_reduction
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (ρ : GaussianInt →+* ZMod q)
    (hρkernel : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (γ : ZMod q → GaussianInt)
    (hγcomplex : ∀ x : ZMod q, (γ x : ℂ) = χ x)
    (hγreduction : ∀ x : ZMod q, ρ (γ x) = x ^ ((q - 1) / 4)) :
    jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2 := by
  obtain ⟨J, u, hJcomplex, hu, hJu⟩ :=
    quartic_jacobi_gaussian_generator_of_reduction q hqmod χ hχ π hπnorm
      ρ hρkernel γ hγcomplex hγreduction
  have hsumcomplex :
      ((∑ x : ZMod q, γ x * γ (1 - x) : GaussianInt) : ℂ) =
        jacobiSum χ χ := by
    simp only [jacobiSum, map_sum, map_mul, hγcomplex]
  have hJsum : J = ∑ x : ZMod q, γ x * γ (1 - x) :=
    GaussianInt.toComplex_injective (hJcomplex.trans hsumcomplex.symm)
  have hJim : (J.im : ZMod 2) = 0 := by
    rw [hJsum]
    exact (quartic_jacobi_parity_of_gaussian_lift q hqmod χ hχ γ hγcomplex).2
  rcases gaussian_associated_eq_sign_of_parity π J u hu hJu
    hπre hπim hJim with hJeq | hJeq
  · rw [← hJcomplex, hJeq]
  · rw [← hJcomplex, hJeq]
    rw [GaussianInt.toComplex_neg]
    ring

/-- The convenient specialization using the canonical Gaussian lift of
`χ`. A concrete split-prime construction only needs to establish the two
properties of `ρ`: its kernel and its action on this lift. -/
theorem quartic_jacobi_square_of_canonical_reduction
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0)
    (ρ : GaussianInt →+* ZMod q)
    (hρkernel : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z)
    (hρcharacter : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4)) :
    jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2 :=
  quartic_jacobi_square_of_reduction q hqmod χ hχ π hπnorm
    hπre hπim ρ hρkernel (quarticGaussianLift q χ hχ)
    (quarticGaussianLift_complex q χ hχ) hρcharacter

/-- Either square root of `-1` in a prime field of order at least five is
a primitive fourth root. -/
theorem gaussian_reduction_root_primitive
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (t : ZMod q) (ht : t * t = -1) : IsPrimitiveRoot t 4 := by
  have hqprime : q.Prime := Fact.out
  have hq5 : 5 ≤ q := by
    have hq2 := hqprime.two_le
    omega
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz
    have hqle2 := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have ht2 : t ^ 2 ≠ 1 := by
    rw [pow_two, ht]
    intro hneg
    apply htwo
    linear_combination -hneg
  have ht4 : t ^ 4 = 1 := by
    calc
      t ^ 4 = (t * t) * (t * t) := by ring
      _ = (-1 : ZMod q) * (-1) := by rw [ht]
      _ = 1 := by ring
  apply IsPrimitiveRoot.iff_orderOf.mpr
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4) ht4
  intro p hp hp4
  have hp2 : p = 2 := by
    have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hp4
    have hge : 2 ≤ p := hp.two_le
    have hp3 : p ≠ 3 := by
      intro he
      subst p
      norm_num at hp4
    have hp4ne : p ≠ 4 := by
      intro he
      subst p
      norm_num at hp
    omega
  subst p
  simpa using ht2

/-- For a generator of the multiplicative group modulo `q`, its quartic
power-residue value is one of the four powers of the chosen Gaussian root
of `-1`, with an exponent less than four. -/
theorem gaussian_quartic_generator_exponent
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (t : ZMod q) (ht : t * t = -1)
    (g : (ZMod q)ˣ) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ j : ℕ, j < 4 ∧ t ^ j = (g : ZMod q) ^ ((q - 1) / 4) := by
  have hqprime : q.Prime := Fact.out
  have hq5 : 5 ≤ q := by
    have hq2 := hqprime.two_le
    omega
  have horder : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      Nat.card_eq_fintype_card, ZMod.card_units]
  have hrootg : IsPrimitiveRoot (g : ZMod q) (q - 1) := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    simpa [orderOf_units] using horder
  have hfactor : q - 1 = ((q - 1) / 4) * 4 := by omega
  have hβroot : IsPrimitiveRoot
      ((g : ZMod q) ^ ((q - 1) / 4)) 4 :=
    IsPrimitiveRoot.pow (by omega : 0 < q - 1) hrootg hfactor
  exact (gaussian_reduction_root_primitive q hqmod t ht).eq_pow_of_pow_eq_one
    hβroot.pow_eq_one

/-- The orientation of a Gaussian reduction determines an order-four
complex character, specified by its value at a chosen generator. -/
theorem exists_quartic_character_matching_generator
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (t : ZMod q) (ht : t * t = -1)
    (g : (ZMod q)ˣ) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ χ : MulChar (ZMod q) ℂ,
      ∃ hχ : orderOf χ = 4,
        gaussianReduction q t ht
          (quarticGaussianLift q χ hχ (g : ZMod q)) =
          (g : ZMod q) ^ ((q - 1) / 4) := by
  classical
  obtain ⟨j, hjlt, hj⟩ := gaussian_quartic_generator_exponent q hqmod t ht g hg
  let ζ : ℂˣ := Units.mk0 (Complex.I ^ j)
    (pow_ne_zero _ Complex.I_ne_zero)
  have hζ4 : ζ ^ 4 = 1 := by
    apply Units.ext
    change (Complex.I ^ j) ^ 4 = 1
    rw [← pow_mul, mul_comm, pow_mul,
      Complex.isPrimitiveRoot_I.pow_eq_one, one_pow]
  have hcard : 4 ∣ Fintype.card (ZMod q)ˣ := by
    rw [ZMod.card_units]
    omega
  have hζcard : ζ ∈ rootsOfUnity (Fintype.card (ZMod q)ˣ) ℂ := by
    rw [mem_rootsOfUnity]
    obtain ⟨m, hm⟩ := hcard
    rw [hm, pow_mul, hζ4, one_pow]
  let χ : MulChar (ZMod q) ℂ := MulChar.ofRootOfUnity hζcard hg
  have hχg : χ (g : ZMod q) = Complex.I ^ j := by
    simpa [χ, ζ] using (MulChar.ofRootOfUnity_spec hζcard hg)
  have hjprimitive : IsPrimitiveRoot (t ^ j) 4 := by
    rw [hj]
    have hqprime : q.Prime := Fact.out
    have hq5 : 5 ≤ q := by
      have hq2 := hqprime.two_le
      omega
    have horder : orderOf g = q - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg,
        Nat.card_eq_fintype_card, ZMod.card_units]
    have hrootg : IsPrimitiveRoot (g : ZMod q) (q - 1) := by
      apply IsPrimitiveRoot.iff_orderOf.mpr
      simpa [orderOf_units] using horder
    exact IsPrimitiveRoot.pow (by omega : 0 < q - 1) hrootg
      (by omega : q - 1 = ((q - 1) / 4) * 4)
  have hjcop : j.Coprime 4 :=
    ((gaussian_reduction_root_primitive q hqmod t ht).pow_iff_coprime
      (by decide) j).mp hjprimitive
  have hIprimitive : IsPrimitiveRoot (Complex.I ^ j) 4 :=
    Complex.isPrimitiveRoot_I.pow_of_coprime j hjcop
  have hχ4 : χ ^ 4 = 1 := by
    apply (MulChar.eq_iff hg _ _).2
    have hval4 : (Complex.I ^ j) ^ 4 = 1 := hIprimitive.pow_eq_one
    simpa [MulChar.pow_apply_coe, hχg] using hval4
  have hχ2 : χ ^ 2 ≠ 1 := by
    intro hχsq
    have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ (g : ZMod q)) hχsq
    have hval2 : (Complex.I ^ j) ^ 2 ≠ 1 :=
      hIprimitive.pow_ne_one_of_pos_of_lt (by decide) (by decide)
    apply hval2
    simpa [MulChar.pow_apply_coe, hχg] using hv
  have hχorder : orderOf χ = 4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4) hχ4
    intro p hp hp4
    have hp2 : p = 2 := by
      have hle : p ≤ 4 := Nat.le_of_dvd (by decide) hp4
      have hge : 2 ≤ p := hp.two_le
      have hp3 : p ≠ 3 := by
        intro he
        subst p
        norm_num at hp4
      have hp4ne : p ≠ 4 := by
        intro he
        subst p
        norm_num at hp
      omega
    subst p
    exact hχ2
  refine ⟨χ, hχorder, ?_⟩
  have hγg : quarticGaussianLift q χ hχorder (g : ZMod q) =
      (⟨0, 1⟩ : GaussianInt) ^ j := by
    apply GaussianInt.toComplex_injective
    rw [quarticGaussianLift_complex, hχg, map_pow]
    simp [GaussianInt.toComplex_def]
  rw [hγg, map_pow]
  simpa [gaussianReduction, Zsqrtd.lift] using hj

/-- The oriented Gaussian reduction determines a quartic character whose
Gaussian lift reduces to the fourth-power residue symbol at every residue. -/
theorem exists_quartic_character_matching_reduction
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (t : ZMod q) (ht : t * t = -1) :
    ∃ χ : MulChar (ZMod q) ℂ,
      ∃ hχ : orderOf χ = 4,
        ∀ x : ZMod q,
          gaussianReduction q t ht (quarticGaussianLift q χ hχ x) =
            x ^ ((q - 1) / 4) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  obtain ⟨χ, hχ, hgen⟩ :=
    exists_quartic_character_matching_generator q hqmod t ht g hg
  refine ⟨χ, hχ, ?_⟩
  let θ : ZMod q →* ZMod q :=
    (gaussianReduction q t ht).toMonoidHom.comp
      (quarticGaussianLiftHom q χ hχ)
  let f : (ZMod q)ˣ →* (ZMod q)ˣ := Units.map θ
  let p : (ZMod q)ˣ →* (ZMod q)ˣ := powMonoidHom ((q - 1) / 4)
  have hfg : f g = p g := by
    apply Units.ext
    simpa [f, p, θ, quarticGaussianLiftHom] using hgen
  have hfp : f = p := (MonoidHom.eq_iff_eq_on_generator hg f p).2 hfg
  intro x
  by_cases hx : x = 0
  · subst x
    have hkpos : 0 < (q - 1) / 4 := by
      have hq2 := (Fact.out : q.Prime).two_le
      omega
    rw [quarticGaussianLift_zero, map_zero,
      zero_pow (Nat.ne_of_gt hkpos)]
  · let ux : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hux : (ux : ZMod q) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    have h := congrArg (fun m : (ZMod q)ˣ →* (ZMod q)ˣ =>
      (m ux : ZMod q)) hfp
    simpa [f, p, θ, quarticGaussianLiftHom, hux] using h

/-- At each Gaussian prime of rational norm `q ≡ 1 (mod 4)`, the
associated quartic residue character has Jacobi square equal to the square
of the odd-real, even-imaginary generator. -/
theorem exists_quartic_character_jacobi_square_at_prime
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) :
    ∃ χ : MulChar (ZMod q) ℂ,
      ∃ _hχ : orderOf χ = 4,
        jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2 := by
  have hπabs : π.norm.natAbs = q := by
    rw [← GaussianInt.abs_natCast_norm, hπnorm]
    simp
  obtain ⟨t, ht, hπt⟩ := exists_gaussian_reduction_at_prime q π hπabs
  obtain ⟨χ, hχ, hρcharacter⟩ :=
    exists_quartic_character_matching_reduction q hqmod t ht
  refine ⟨χ, hχ, ?_⟩
  apply quartic_jacobi_square_of_canonical_reduction q hqmod χ hχ π
    hπnorm hπre hπim (gaussianReduction q t ht)
  · intro z
    exact gaussianReduction_zero_iff_dvd q t ht π hπabs
      (by simpa using hπt) z
  · exact hρcharacter

/-- A residue-character witness retains the reduction identity as well as
the Jacobi evaluation. This is the form used to compare the character with
the ideal-theoretic quartic symbol. -/
theorem exists_quartic_residue_character_at_prime
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) :
    ∃ ρ : GaussianInt →+* ZMod q,
      (∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z) ∧
      ∃ χ : MulChar (ZMod q) ℂ,
        ∃ hχ : orderOf χ = 4,
          (∀ x : ZMod q,
            ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4)) ∧
          jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2 := by
  have hπabs : π.norm.natAbs = q := by
    rw [← GaussianInt.abs_natCast_norm, hπnorm]
    simp
  obtain ⟨t, ht, hπt⟩ := exists_gaussian_reduction_at_prime q π hπabs
  let ρ := gaussianReduction q t ht
  have hρkernel : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z := by
    intro z
    exact gaussianReduction_zero_iff_dvd q t ht π hπabs
      (by simpa using hπt) z
  obtain ⟨χ, hχ, hρchar⟩ :=
    exists_quartic_character_matching_reduction q hqmod t ht
  refine ⟨ρ, hρkernel, χ, hχ, hρchar, ?_⟩
  exact quartic_jacobi_square_of_canonical_reduction q hqmod χ hχ π
    hπnorm hπre hπim ρ hρkernel hρchar

/-- A quartic residue character attached to a normalized Gaussian prime.
The existence theorem fixes the orientation by finite-field reduction. -/
noncomputable def quarticCharacterAtGaussianPrime
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) : MulChar (ZMod q) ℂ :=
  Classical.choose
    (exists_quartic_character_jacobi_square_at_prime q hqmod π
      hπnorm hπre hπim)

theorem quarticCharacterAtGaussianPrime_order
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) :
    orderOf (quarticCharacterAtGaussianPrime q hqmod π hπnorm hπre hπim) = 4 :=
  Classical.choose
    (Classical.choose_spec
      (exists_quartic_character_jacobi_square_at_prime q hqmod π
        hπnorm hπre hπim))

theorem quarticCharacterAtGaussianPrime_jacobi_square
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (π : GaussianInt) (hπnorm : π.norm = q)
    (hπre : (π.re : ZMod 2) = 1)
    (hπim : (π.im : ZMod 2) = 0) :
    jacobiSum
        (quarticCharacterAtGaussianPrime q hqmod π hπnorm hπre hπim)
        (quarticCharacterAtGaussianPrime q hqmod π hπnorm hπre hπim) ^ 2 =
      (π : ℂ) ^ 2 :=
  Classical.choose_spec
    (Classical.choose_spec
      (exists_quartic_character_jacobi_square_at_prime q hqmod π
        hπnorm hπre hπim))

end Erdos940.Quartic
