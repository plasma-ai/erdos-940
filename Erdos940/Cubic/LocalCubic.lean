module

public import Erdos940.Statement
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cubic solution counts for Erdős Problem 940

These are the local counts in §3 of Beyer de Ryke's proof of a positive density
of integers that are not sums of three cube-full numbers.  The coefficients
will later be the canonical 4-full parts of the three summands.

The two character estimates below are stated separately from the elementary
change of variables and the elementary cubic-fiber bound.  The latter is valid
over any finite field; the character estimates require a prime `q ≡ 1 (mod 3)`.

The character identities and the resulting local bounds are proved in this module.
-/

@[expose] public section

namespace Erdos940

/-- The number `N_q(u; a)` in §3, generalized to an arbitrary finite field.
The three coordinates of `a` are the coefficients of the three cubes. -/
noncomputable def localCubicCount (F : Type*) [Field F] [Fintype F]
    (u : F) (a : Fin 3 → F) : ℕ := by
  classical
  exact Fintype.card {x : Fin 3 → F // ∑ i, a i * x i ^ 3 = u}

/-- The unweighted count `N_q(u)` in Lemma 3.1. -/
noncomputable def threeCubesCount (F : Type*) [Field F] [Fintype F]
    (u : F) : ℕ :=
  localCubicCount F u (fun _ => 1)

/-- A noncube in a field. In particular, zero does not satisfy this predicate. -/
def IsNoncube {F : Type*} [Field F] (u : F) : Prop :=
  ¬ ∃ x : F, x ^ 3 = u

theorem IsNoncube.ne_zero {F : Type*} [Field F] {u : F}
    (hu : IsNoncube u) : u ≠ 0 := by
  intro hzero
  apply hu
  exact ⟨0, by simp [hzero]⟩

/-- The elementary fact used in Lemma 3.2: a cubic equation has at most three
solutions in a field. -/
theorem cubicFiber_card_le_three (F : Type*) [Field F] [Fintype F] (u : F) :
    Nat.card {x : F // x ^ 3 = u} ≤ 3 := by
  classical
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  have hroots :
      (Finset.univ.filter fun x : F => x ^ 3 = u).val ⊆
        ((Polynomial.X : Polynomial F) ^ 3 - Polynomial.C u).roots := by
    intro x hx
    have hx' : x ^ 3 = u :=
      by simpa only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact (Polynomial.mem_roots_sub_C (by simp)).2 (by simpa using hx')
  simpa only [Polynomial.natDegree_X_pow_sub_C] using
    Polynomial.card_le_degree_of_subset_roots hroots

/-- Lemma 3.1, inequality (5), in natural-number form. The additive form
avoids truncated subtraction: it says `N_q(u) ≤ q² - 2q`. -/
theorem exists_cubic_character (q : ℕ) [Fact q.Prime]
    (hq : q % 3 = 1) :
    ∃ χ : MulChar (ZMod q) ℂ, orderOf χ = 3 := by
  have hdiv : 3 ∣ Fintype.card (ZMod q) - 1 := by
    have hcard : Fintype.card (ZMod q) = q := ZMod.card q
    rw [hcard]
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  exact MulChar.exists_mulChar_orderOf (ZMod q) hdiv
    (Complex.isPrimitiveRoot_exp 3 (by decide))

theorem gaussSum_norm_eq_sqrt_card
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have hmul := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq χ ψ] at hmul
  have hnorm := congrArg norm hmul
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    simpa only [norm_mul, norm_star, Complex.norm_natCast, pow_two] using hnorm
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg (Fintype.card F : ℝ),
    norm_nonneg (gaussSum χ ψ)]

private theorem cubic_character_neg_one (q : ℕ) [Fact q.Prime]
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 3) :
    χ (-1) = 1 := by
  apply MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3)
  simpa [hχ] using pow_orderOf_eq_one χ

private theorem prime_mod_three_one_ge_seven (q : ℕ) [Fact q.Prime]
    (hq : q % 3 = 1) : 7 ≤ q := by
  have hp : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hp.two_le
  by_contra h
  have hq6 : q ≤ 6 := by omega
  interval_cases q <;> norm_num at hp hq
  exact (by decide : ¬ Nat.Prime 4) hp

/-- The kernel of an order-three character on the nonzero residues is exactly
the subgroup of cubes. This is the cyclic-group step behind the cubic-root
count, independent of the additive-character calculations. -/
private theorem cubic_character_units_ker_eq_cubes
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 3) :
    χ.toUnitHom.ker =
      (powMonoidHom 3 : (ZMod q)ˣ →* (ZMod q)ˣ).range := by
  classical
  let G := (ZMod q)ˣ
  have hdiv : 3 ∣ Nat.card G := by
    have h := MulChar.orderOf_dvd_card_sub_one (ZMod q) χ
    change 3 ∣ Nat.card (ZMod q)ˣ
    rw [Nat.card_units]
    simpa only [hχ, Nat.card_eq_fintype_card] using h
  have hpowindex :
      (powMonoidHom 3 : G →* G).range.index = 3 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd]
    exact hdiv
  have hkerindex : χ.toUnitHom.ker.index = 3 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hχne : χ ≠ 1 := by
      intro he
      simp [he] at hχ
    have hgenne : χ.toUnitHom g ≠ 1 := by
      intro he
      apply hχne
      apply (MulChar.eq_iff hg χ 1).2
      have hv := congrArg Units.val he
      simpa using hv
    have hchar : χ ^ 3 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hgenpow : (χ.toUnitHom g) ^ 3 = 1 := by
      apply Units.ext
      have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ (g : ZMod q)) hchar
      simpa [MulChar.pow_apply_coe] using hv
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hgenorder : orderOf (χ.toUnitHom g) = 3 :=
      orderOf_eq_prime hgenpow hgenne
    have hrange : χ.toUnitHom.range = Subgroup.zpowers (χ.toUnitHom g) := by
      rw [MonoidHom.range_eq_map,
        ← (Subgroup.zpowers g).eq_top_iff'.mpr hg,
        MonoidHom.map_zpowers]
    rw [Subgroup.index_ker, hrange, Nat.card_zpowers, hgenorder]
  have hle : (powMonoidHom 3 : G →* G).range ≤ χ.toUnitHom.ker := by
    rintro _ ⟨x, rfl⟩
    change χ.toUnitHom (x ^ 3) = 1
    rw [map_pow]
    have hchar : χ ^ 3 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hx := congrArg (fun φ : MulChar (ZMod q) ℂ => φ (x : ZMod q)) hchar
    apply Units.ext
    simpa [MulChar.pow_apply_coe] using hx
  have hcardpow : Nat.card (powMonoidHom 3 : G →* G).range * 3 = Nat.card G := by
    simpa only [hpowindex] using
      (powMonoidHom 3 : G →* G).range.card_mul_index
  have hcardker : Nat.card χ.toUnitHom.ker * 3 = Nat.card G := by
    simpa only [hkerindex] using χ.toUnitHom.ker.card_mul_index
  have hcard : Nat.card χ.toUnitHom.ker ≤
      Nat.card (powMonoidHom 3 : G →* G).range := by
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

private theorem cubic_unit_fiber_card_of_exists
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 3) (y : (ZMod q)ˣ)
    (hy : ∃ x : (ZMod q)ˣ, x ^ 3 = y) :
    Nat.card {x : (ZMod q)ˣ // x ^ 3 = y} = 3 := by
  classical
  let G := (ZMod q)ˣ
  have hdiv : 3 ∣ Nat.card G := by
    have h := MulChar.orderOf_dvd_card_sub_one (ZMod q) χ
    change 3 ∣ Nat.card (ZMod q)ˣ
    rw [Nat.card_units]
    simpa only [hχ, Nat.card_eq_fintype_card] using h
  have hker : Nat.card (powMonoidHom 3 : G →* G).ker = 3 := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right_iff_dvd]
    exact hdiv
  have hrange : y ∈ Set.range (powMonoidHom 3 : G →* G) := hy
  have hone : (1 : G) ∈ Set.range (powMonoidHom 3 : G →* G) :=
    ⟨1, by simp⟩
  have hfiber := MonoidHom.card_fiber_eq_of_mem_range
    (powMonoidHom 3 : G →* G) hrange hone
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hker_card :
      (Finset.univ.filter fun x : G => x ^ 3 = 1).card =
        Nat.card (powMonoidHom 3 : G →* G).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  simpa only [powMonoidHom_apply, hker_card, hker] using hfiber

/-- Equation (6)'s cubic-root multiplicity identity. The cyclic group of
nonzero residues has a cube map with fibers of size three, and the two
nontrivial character values distinguish its image. -/
theorem cubic_root_count_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 3) (y : ZMod q) :
    (Nat.card {x : ZMod q // x ^ 3 = y} : ℂ) = 1 + χ y + χ⁻¹ y := by
  classical
  by_cases hy : y = 0
  · subst y
    have hfiber : Nat.card {x : ZMod q // x ^ 3 = 0} = 1 := by
      have hs : (Finset.univ.filter fun x : ZMod q => x ^ 3 = 0) = {0} := by
        ext x
        simp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hs]
      simp
    norm_num [hfiber, MulChar.map_zero]
  let uy : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hy).unit
  have huy : (uy : ZMod q) = y := (isUnit_iff_ne_zero.mpr hy).unit_spec
  have hcharcube : χ y = 1 ↔ ∃ x : ZMod q, x ^ 3 = y := by
    have hker : uy ∈ χ.toUnitHom.ker ↔ χ y = 1 := by
      change χ.toUnitHom uy = 1 ↔ χ y = 1
      constructor
      · intro h
        have hv := congrArg Units.val h
        simpa [huy] using hv
      · intro h
        apply Units.ext
        simpa [huy] using h
    have hrange :
        uy ∈ (powMonoidHom 3 : (ZMod q)ˣ →* (ZMod q)ˣ).range ↔
          ∃ x : ZMod q, x ^ 3 = y := by
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨(v : ZMod q), ?_⟩
        have hv' := congrArg (fun z : (ZMod q)ˣ => (z : ZMod q)) hv
        simpa [huy] using hv'
      · rintro ⟨x, hx⟩
        have hx0 : x ≠ 0 := by
          intro hzero
          apply hy
          simpa [hzero] using hx.symm
        let ux : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hx0).unit
        refine ⟨ux, ?_⟩
        apply Units.ext
        simpa [ux, huy] using hx
    rw [cubic_character_units_ker_eq_cubes q χ hχ] at hker
    exact hker.symm.trans hrange
  by_cases hχy : χ y = 1
  · obtain ⟨x, hx⟩ := hcharcube.mp hχy
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hy
      simpa [hzero] using hx.symm
    let ux : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hx0).unit
    have hux : ux ^ 3 = uy := by
      apply Units.ext
      simpa [ux, huy] using hx
    have hcountunits := cubic_unit_fiber_card_of_exists q χ hχ uy ⟨ux, hux⟩
    let e : {v : (ZMod q)ˣ // v ^ 3 = uy} ≃
        {z : ZMod q // z ^ 3 = y} := {
      toFun v := ⟨(v.1 : ZMod q), by
        have hv := congrArg (fun w : (ZMod q)ˣ => (w : ZMod q)) v.2
        simpa [huy] using hv⟩
      invFun z := by
        have hz0 : z.1 ≠ 0 := by
          intro hzero
          apply hy
          simpa [hzero] using z.2.symm
        let uz : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hz0).unit
        exact ⟨uz, by
          apply Units.ext
          simpa [uz, huy] using z.2⟩
      left_inv v := by
        apply Subtype.ext
        apply Units.ext
        simp
      right_inv z := by
        apply Subtype.ext
        simp
    }
    have hcount : Nat.card {z : ZMod q // z ^ 3 = y} = 3 := by
      calc
        Nat.card {z : ZMod q // z ^ 3 = y} =
            Nat.card {v : (ZMod q)ˣ // v ^ 3 = uy} := Nat.card_congr e.symm
        _ = 3 := hcountunits
    rw [hcount, hχy]
    have hχinv : χ⁻¹ y = 1 := by
      rw [MulChar.inv_apply_eq_inv, hχy]
      simp
    rw [hχinv]
    norm_num
  · have hcount : Nat.card {z : ZMod q // z ^ 3 = y} = 0 := by
      letI : IsEmpty {z : ZMod q // z ^ 3 = y} :=
        ⟨fun z => hχy (hcharcube.mpr ⟨z.1, z.2⟩)⟩
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero
    have hchar : χ ^ 3 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hz3 : (χ y) ^ 3 = 1 := by
      have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ y) hchar
      simpa [MulChar.pow_apply' χ (by decide : 3 ≠ 0),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)] using hv
    have hz_inv : (χ y)⁻¹ = (χ y) ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      calc
        χ y * (χ y) ^ 2 = (χ y) ^ 3 := by ring
        _ = 1 := hz3
    have hfactor : (χ y - 1) * (1 + χ y + (χ y) ^ 2) = 0 := by
      calc
        (χ y - 1) * (1 + χ y + (χ y) ^ 2) = (χ y) ^ 3 - 1 := by ring
        _ = 0 := by rw [hz3]; ring
    have hne : χ y - 1 ≠ 0 := sub_ne_zero.mpr hχy
    have hsum : 1 + χ y + (χ y) ^ 2 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hne
    rw [hcount, MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv, hz_inv]
    simpa only [Nat.cast_zero] using hsum.symm

/-- At a noncube, the two nontrivial cubic-character values sum to `-1`. -/
private theorem cubic_character_noncube_sum
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 3) (u : ZMod q) (hu : IsNoncube u) :
    χ u + χ⁻¹ u = -1 := by
  letI : IsEmpty {x : ZMod q // x ^ 3 = u} :=
    ⟨fun x => hu ⟨x.1, x.2⟩⟩
  have hcount : Nat.card {x : ZMod q // x ^ 3 = u} = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_eq_zero
  have hformula := cubic_root_count_character q χ hχ u
  rw [hcount] at hformula
  norm_num at hformula
  linear_combination -hformula

/-- The cubic exponential sum at a nonzero frequency, expressed as the two
Gauss sums of the cubic characters. This is the bridge from the root-count
identity to the local Fourier estimate. -/
theorem cubic_exponential_sum_eq_gauss
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 3) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (t : ZMod q) (ht : t ≠ 0) :
    (∑ x : ZMod q, ψ (t * x ^ 3)) =
      χ⁻¹ t * gaussSum χ ψ + χ t * gaussSum χ⁻¹ ψ := by
  classical
  have hfiber :
      (∑ x : ZMod q, ψ (t * x ^ 3)) =
        ∑ y : ZMod q, (Nat.card {x : ZMod q // x ^ 3 = y} : ℂ) * ψ (t * y) := by
    calc
      (∑ x : ZMod q, ψ (t * x ^ 3)) =
          ∑ y : ZMod q, ∑ x ∈ (Finset.univ.filter fun x : ZMod q => x ^ 3 = y),
            ψ (t * x ^ 3) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (x ^ 3)) _
      _ = ∑ y : ZMod q, (Nat.card {x : ZMod q // x ^ 3 = y} : ℂ) * ψ (t * y) := by
        apply Finset.sum_congr rfl
        intro y _
        calc
          (∑ x ∈ (Finset.univ.filter fun x : ZMod q => x ^ 3 = y),
              ψ (t * x ^ 3)) =
              (Finset.univ.filter fun x : ZMod q => x ^ 3 = y).card * ψ (t * y) := by
            rw [Finset.sum_congr rfl (fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
              rw [hx])]
            simp
          _ = (Nat.card {x : ZMod q // x ^ 3 = y} : ℂ) * ψ (t * y) := by
            simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hfiber]
  simp_rw [cubic_root_count_character q χ hχ]
  have hzero : (∑ y : ZMod q, ψ (t * y)) = 0 := by
    simpa only [mul_comm t, if_neg ht, Nat.cast_zero] using AddChar.sum_mulShift t hψ
  have hunit : IsUnit t := isUnit_iff_ne_zero.mpr ht
  let ut : (ZMod q)ˣ := hunit.unit
  have hut : (ut : ZMod q) = t := hunit.unit_spec
  have hχsum :
      (∑ y : ZMod q, χ y * ψ (t * y)) = χ⁻¹ t * gaussSum χ ψ := by
    simpa only [gaussSum, AddChar.mulShift_apply, hut, mul_comm t] using
      gaussSum_mulShift_eq χ ψ ut
  have hχinvsum :
      (∑ y : ZMod q, χ⁻¹ y * ψ (t * y)) = χ t * gaussSum χ⁻¹ ψ := by
    simpa only [gaussSum, AddChar.mulShift_apply, hut, mul_comm t, inv_inv] using
      gaussSum_mulShift_eq χ⁻¹ ψ ut
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hχsum, hχinvsum]
  simpa only [one_mul, hzero, zero_add]

/-- Additive orthogonality for the coefficient-weighted cubic count. -/
theorem localCubicCount_fourier
    (F : Type*) [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (u : F) (a : Fin 3 → F) :
    (Fintype.card F : ℂ) * (localCubicCount F u a : ℂ) =
      ∑ s : F, ψ (-s * u) *
        ∏ i : Fin 3, ∑ x : F, ψ (s * a i * x ^ 3) := by
  classical
  have horth (v : F) :
      (∑ s : F, ψ (s * v)) =
        if v = 0 then (Fintype.card F : ℂ) else 0 :=
    by simpa using AddChar.sum_mulShift v hψ
  have hcount :
      (localCubicCount F u a : ℂ) =
        ∑ x : Fin 3 → F,
          if ∑ i, a i * x i ^ 3 = u then (1 : ℂ) else 0 := by
    simp [localCubicCount, Fintype.card_subtype]
  have hphase (s : F) (x : Fin 3 → F) :
      ψ (-s * u) * (∏ i : Fin 3, ψ (s * a i * x i ^ 3)) =
        ψ (s * ((∑ i : Fin 3, a i * x i ^ 3) - u)) := by
    have hprod :
        (∏ i : Fin 3, ψ (s * a i * x i ^ 3)) =
          ψ (∑ i : Fin 3, s * a i * x i ^ 3) := by
      simp only [Fin.prod_univ_three, Fin.sum_univ_three,
        AddChar.map_add_eq_mul]
    rw [hprod, ← ψ.map_add_eq_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    simp_rw [mul_assoc]
    ring
  calc
    (Fintype.card F : ℂ) * (localCubicCount F u a : ℂ) =
        ∑ x : Fin 3 → F,
          if ∑ i, a i * x i ^ 3 = u then (Fintype.card F : ℂ) else 0 := by
      rw [hcount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x : Fin 3 → F,
          ∑ s : F, ψ (s * ((∑ i, a i * x i ^ 3) - u)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [horth]
      simp only [sub_eq_zero]
    _ = ∑ s : F, ψ (-s * u) *
          ∏ i : Fin 3, ∑ x : F, ψ (s * a i * x ^ 3) := by
      rw [Finset.sum_comm]
      simp_rw [← hphase]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      rw [Fintype.prod_sum]

/-- Equation (4) of Beyer de Ryke, stated for any primitive additive
character. The right side is unchanged by rescaling the additive character,
since the multiplicative character has order three. -/
private theorem threeCubesCount_gauss_formula
    (q : ℕ) [Fact q.Prime]
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 3)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (u : ZMod q) (hu : u ≠ 0) :
    (threeCubesCount (ZMod q) u : ℂ) =
      (q : ℂ) ^ 2 + 3 * q * (χ u + χ⁻¹ u) -
        (gaussSum χ ψ ^ 3 + gaussSum χ⁻¹ ψ ^ 3) / q := by
  classical
  let τ : ℂ := gaussSum χ ψ
  let ρ : ℂ := gaussSum χ⁻¹ ψ
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have hχne : χ ≠ 1 := by
    intro he
    simp [he] at hχ
  have hχpow : χ ^ 3 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχ2 : χ ^ 2 = χ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ * χ ^ 2 = χ ^ 3 := by
        rw [pow_succ]
        exact mul_comm _ _
      _ = 1 := hχpow
  have hτprod : τ * ρ = (q : ℂ) := by
    have hp := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχne hψ
    simpa [τ, ρ, hχ, hχ2, hcard, cubic_character_neg_one q χ hχ] using hp
  have hfourier :
      (q : ℂ) * (threeCubesCount (ZMod q) u : ℂ) =
        ∑ s : ZMod q, ψ (-s * u) *
          (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3 := by
    simpa [threeCubesCount, hcard, Fin.prod_univ_three, pow_three,
      mul_assoc] using
      localCubicCount_fourier (ZMod q) ψ hψ u (fun _ => 1)
  have hzero : (∑ x : ZMod q, ψ ((0 : ZMod q) * x ^ 3)) = (q : ℂ) := by
    simp [hcard]
  have hcube (s : ZMod q) (hs : s ≠ 0) :
      (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3 =
        τ ^ 3 + ρ ^ 3 + 3 * q * (τ * χ⁻¹ s + ρ * χ s) := by
    have hχs3 : (χ s) ^ 3 = 1 := by
      have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ s) hχpow
      simpa [MulChar.pow_apply' χ (by decide : 3 ≠ 0),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hs)] using hv
    have hχinvs3 : (χ⁻¹ s) ^ 3 = 1 := by
      rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv, inv_pow, hχs3, inv_one]
    have hχprod : χ⁻¹ s * χ s = 1 := by
      rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
      exact inv_mul_cancel₀ ((MulChar.apply_ne_zero_iff).2
        (isUnit_iff_ne_zero.mpr hs))
    rw [cubic_exponential_sum_eq_gauss q χ hχ ψ hψ s hs]
    calc
      (χ⁻¹ s * τ + χ s * ρ) ^ 3 =
          τ ^ 3 * (χ⁻¹ s) ^ 3 + ρ ^ 3 * (χ s) ^ 3 +
            3 * (τ * ρ) * (τ * χ⁻¹ s + ρ * χ s) *
              (χ⁻¹ s * χ s) := by ring
      _ = τ ^ 3 + ρ ^ 3 + 3 * q * (τ * χ⁻¹ s + ρ * χ s) := by
        rw [hχinvs3, hχs3, hχprod, hτprod]
        ring
  have hψsum : (∑ s : ZMod q, ψ (-s * u)) = 0 := by
    have hz := AddChar.sum_mulShift (-u) hψ
    simp only [if_neg (neg_ne_zero.mpr hu), Nat.cast_zero] at hz
    calc
      (∑ s : ZMod q, ψ (-s * u)) =
          ∑ s : ZMod q, ψ (s * (-u)) := by
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        ring
      _ = 0 := hz
  have hgaussShift (φ : MulChar (ZMod q) ℂ) (hφneg : φ (-1) = 1) :
      (∑ s : ZMod q, ψ (-s * u) * φ s) =
        φ⁻¹ u * gaussSum φ ψ := by
    let vu : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hu)).unit
    have hv : (vu : ZMod q) = -u :=
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hu)).unit_spec
    have hφinvneg : φ⁻¹ (-1) = 1 := by
      rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv, hφneg]
      simp
    calc
      (∑ s : ZMod q, ψ (-s * u) * φ s) =
          gaussSum φ (ψ.mulShift vu) := by
        unfold gaussSum
        apply Finset.sum_congr rfl
        intro s _
        rw [AddChar.mulShift_apply, hv]
        have hphase : -s * u = s * (-u) := by ring
        rw [hphase]
        ring
      _ = φ⁻¹ vu * gaussSum φ ψ := gaussSum_mulShift_eq φ ψ vu
      _ = φ⁻¹ u * gaussSum φ ψ := by
        rw [hv, show -u = (-1) * u by ring, map_mul, hφinvneg, one_mul]
  have hgaussχ :
      (∑ s : ZMod q, ψ (-s * u) * χ s) = χ⁻¹ u * τ := by
    simpa [τ] using hgaussShift χ (cubic_character_neg_one q χ hχ)
  have hgaussχinv :
      (∑ s : ZMod q, ψ (-s * u) * χ⁻¹ s) = χ u * ρ := by
    have hneg : χ⁻¹ (-1) = 1 := by
      rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv,
        cubic_character_neg_one q χ hχ]
      simp
    simpa [ρ] using hgaussShift χ⁻¹ hneg
  let E : Finset (ZMod q) := Finset.univ.erase 0
  have hψerase : (∑ s ∈ E, ψ (-s * u)) = -1 := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
      (f := fun s => ψ (-s * u)) (Finset.mem_univ 0)
    have hsplit' : (∑ s ∈ E, ψ (-s * u)) + 1 = 0 := by
      simpa only [neg_zero, zero_mul, AddChar.map_zero_eq_one] using
        hsplit.trans hψsum
    linear_combination hsplit'
  have hχerase :
      (∑ s ∈ E, ψ (-s * u) * χ s) = χ⁻¹ u * τ := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
      (f := fun s => ψ (-s * u) * χ s) (Finset.mem_univ 0)
    simpa only [neg_zero, zero_mul, MulChar.map_zero, mul_zero, add_zero] using
      hsplit.trans hgaussχ
  have hχinverase :
      (∑ s ∈ E, ψ (-s * u) * χ⁻¹ s) = χ u * ρ := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
      (f := fun s => ψ (-s * u) * χ⁻¹ s) (Finset.mem_univ 0)
    simpa only [neg_zero, zero_mul, MulChar.map_zero, mul_zero, add_zero] using
      hsplit.trans hgaussχinv
  have hE :
      (∑ s ∈ E, ψ (-s * u) * (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3) =
        -(τ ^ 3 + ρ ^ 3) +
          3 * q * (τ * (χ u * ρ) + ρ * (χ⁻¹ u * τ)) := by
    calc
      (∑ s ∈ E, ψ (-s * u) * (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3) =
          ∑ s ∈ E, ψ (-s * u) *
            (τ ^ 3 + ρ ^ 3 + 3 * q * (τ * χ⁻¹ s + ρ * χ s)) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hcube s (Finset.ne_of_mem_erase hs)]
      _ = (τ ^ 3 + ρ ^ 3) * (∑ s ∈ E, ψ (-s * u)) +
          3 * q * τ * (∑ s ∈ E, ψ (-s * u) * χ⁻¹ s) +
          3 * q * ρ * (∑ s ∈ E, ψ (-s * u) * χ s) := by
        have hterm (s : ZMod q) :
            ψ (-s * u) *
              (τ ^ 3 + ρ ^ 3 + 3 * q * (τ * χ⁻¹ s + ρ * χ s)) =
              (τ ^ 3 + ρ ^ 3) * ψ (-s * u) +
                3 * q * τ * (ψ (-s * u) * χ⁻¹ s) +
                3 * q * ρ * (ψ (-s * u) * χ s) := by ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = -(τ ^ 3 + ρ ^ 3) +
          3 * q * (τ * (χ u * ρ) + ρ * (χ⁻¹ u * τ)) := by
        rw [hψerase, hχinverase, hχerase]
        ring
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
    (f := fun s => ψ (-s * u) * (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3)
    (Finset.mem_univ 0)
  have hqN :
      (q : ℂ) * (threeCubesCount (ZMod q) u : ℂ) =
        (q : ℂ) ^ 3 - (τ ^ 3 + ρ ^ 3) +
          3 * q * (τ * (χ u * ρ) + ρ * (χ⁻¹ u * τ)) := by
    calc
      (q : ℂ) * (threeCubesCount (ZMod q) u : ℂ) =
          ∑ s : ZMod q, ψ (-s * u) *
            (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3 := hfourier
      _ = (∑ s ∈ E, ψ (-s * u) *
            (∑ x : ZMod q, ψ (s * x ^ 3)) ^ 3) +
          ψ (-(0 : ZMod q) * u) *
            (∑ x : ZMod q, ψ ((0 : ZMod q) * x ^ 3)) ^ 3 := hsplit.symm
      _ = (q : ℂ) ^ 3 - (τ ^ 3 + ρ ^ 3) +
          3 * q * (τ * (χ u * ρ) + ρ * (χ⁻¹ u * τ)) := by
        rw [hE, hzero]
        simp
        ring
  have hqN' :
      (q : ℂ) * (threeCubesCount (ZMod q) u : ℂ) =
        (q : ℂ) ^ 3 + 3 * (q : ℂ) ^ 2 * (χ u + χ⁻¹ u) -
          (τ ^ 3 + ρ ^ 3) := by
    calc
      _ = (q : ℂ) ^ 3 - (τ ^ 3 + ρ ^ 3) +
          3 * q * (τ * (χ u * ρ) + ρ * (χ⁻¹ u * τ)) := hqN
      _ = (q : ℂ) ^ 3 - (τ ^ 3 + ρ ^ 3) +
          3 * q * ((τ * ρ) * (χ u + χ⁻¹ u)) := by ring
      _ = (q : ℂ) ^ 3 + 3 * (q : ℂ) ^ 2 * (χ u + χ⁻¹ u) -
          (τ ^ 3 + ρ ^ 3) := by rw [hτprod]; ring
  have hqC : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  apply (mul_left_cancel₀ hqC)
  calc
    (q : ℂ) * (threeCubesCount (ZMod q) u : ℂ) =
        (q : ℂ) ^ 3 + 3 * (q : ℂ) ^ 2 * (χ u + χ⁻¹ u) -
          (τ ^ 3 + ρ ^ 3) := hqN'
    _ = (q : ℂ) * ((q : ℂ) ^ 2 + 3 * q * (χ u + χ⁻¹ u) -
          (τ ^ 3 + ρ ^ 3) / q) := by field_simp

private theorem cubic_gauss_error_norm_bound
    (q : ℕ) (hq : 0 < q) (τ τ' : ℂ)
    (hτ : ‖τ‖ = Real.sqrt q) (hτ' : ‖τ'‖ = Real.sqrt q) :
    ‖(τ ^ 3 + τ' ^ 3) / (q : ℂ)‖ ≤ 2 * Real.sqrt q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsqrt : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt (le_of_lt hqpos)
  have hpow : Real.sqrt (q : ℝ) ^ 3 = (q : ℝ) * Real.sqrt q := by
    calc
      Real.sqrt (q : ℝ) ^ 3 = Real.sqrt q ^ 2 * Real.sqrt q := by ring
      _ = (q : ℝ) * Real.sqrt q := by rw [hsqrt]
  have hnum : ‖τ ^ 3 + τ' ^ 3‖ ≤ 2 * (q : ℝ) * Real.sqrt q := by
    calc
      ‖τ ^ 3 + τ' ^ 3‖ ≤ ‖τ ^ 3‖ + ‖τ' ^ 3‖ := norm_add_le _ _
      _ = 2 * (q : ℝ) * Real.sqrt q := by
        rw [norm_pow, norm_pow, hτ, hτ', hpow]
        ring
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hqpos).2
  nlinarith [hnum]

theorem threeCubesCount_noncube_bound (q : ℕ) [Fact q.Prime]
    (hq : q % 3 = 1) (u : ZMod q) (hu : IsNoncube u) :
    threeCubesCount (ZMod q) u + 2 * q ≤ q * q := by
  obtain ⟨χ, hχ⟩ := exists_cubic_character q hq
  let ψ : AddChar (ZMod q) ℂ :=
    AddChar.FiniteField.primitiveChar_to_Complex (ZMod q)
  have hψ : ψ.IsPrimitive :=
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod q)
  have hχne : χ ≠ 1 := by
    intro heq
    simp [heq] at hχ
  have hχinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχne
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have hτ : ‖gaussSum χ ψ‖ = Real.sqrt q := by
    simpa [hcard] using gaussSum_norm_eq_sqrt_card (ZMod q) χ hχne ψ hψ
  have hτ' : ‖gaussSum χ⁻¹ ψ‖ = Real.sqrt q := by
    simpa [hcard] using gaussSum_norm_eq_sqrt_card (ZMod q) χ⁻¹ hχinv ψ hψ
  let E : ℂ := (gaussSum χ ψ ^ 3 + gaussSum χ⁻¹ ψ ^ 3) / q
  have hq7 := prime_mod_three_one_ge_seven q hq
  have hqpos : 0 < q := by omega
  have hE : ‖E‖ ≤ 2 * Real.sqrt q :=
    cubic_gauss_error_norm_bound q hqpos _ _ hτ hτ'
  have hformula :=
    threeCubesCount_gauss_formula q χ hχ ψ hψ u hu.ne_zero
  rw [cubic_character_noncube_sum q χ hχ u hu] at hformula
  have hformula' : (threeCubesCount (ZMod q) u : ℂ) =
      (q : ℂ) ^ 2 - 3 * q - E := by
    dsimp [E]
    convert hformula using 1 <;> ring
  have hRe := congrArg Complex.re hformula'
  have hpow_re : ((q : ℂ) ^ 2).re = (q : ℝ) ^ 2 := by
    norm_num [pow_two, Complex.mul_re]
  have hRe' : (threeCubesCount (ZMod q) u : ℝ) =
      (q : ℝ) ^ 2 - 3 * q - E.re := by
    simpa [hpow_re] using hRe
  have hElower : -2 * Real.sqrt (q : ℝ) ≤ E.re := by
    have hlow := (abs_le.mp (Complex.abs_re_le_norm E)).1
    linarith
  have hqR : (7 : ℝ) ≤ q := by exact_mod_cast hq7
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hsqrt_sq := Real.sq_sqrt hqnonneg
  have hsqrt_nonneg := Real.sqrt_nonneg (q : ℝ)
  have hsqrt_ge_two : (2 : ℝ) ≤ Real.sqrt q := by nlinarith
  have hsqrt_le : 2 * Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
    nlinarith [mul_nonneg hsqrt_nonneg (sub_nonneg.mpr hsqrt_ge_two)]
  have hmainR :
      (threeCubesCount (ZMod q) u : ℝ) + 2 * (q : ℝ) ≤ (q : ℝ) * q := by
    nlinarith
  exact_mod_cast hmainR

/-- Changing variables `yᵢ = bᵢ xᵢ` removes coefficients that are nonzero
cubes. This is the step used after choosing splitting primes in §5. -/
theorem localCubicCount_eq_threeCubesCount_of_cube_coefficients
    (F : Type*) [Field F] [Fintype F] (u : F) (a : Fin 3 → F)
    (ha : ∀ i, ∃ b : F, b ≠ 0 ∧ b ^ 3 = a i) :
    localCubicCount F u a = threeCubesCount F u := by
  classical
  choose b hb0 hba using ha
  let e : (Fin 3 → F) ≃ (Fin 3 → F) :=
    Equiv.piCongrRight (fun i => Equiv.mulLeft₀ (b i) (hb0 i))
  have he (x : Fin 3 → F) (i : Fin 3) : e x i = b i * x i := by
    simp [e, Equiv.mulLeft₀]
  have hsum (x : Fin 3 → F) :
      (∑ i, a i * x i ^ 3) = ∑ i, (e x i) ^ 3 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [he x i, mul_pow, hba i]
  have hpred (x : Fin 3 → F) :
      (∑ i, a i * x i ^ 3 = u) ↔
        (∑ i, (1 : F) * (e x i) ^ 3 = u) := by
    simp only [one_mul, ← hsum x]
  exact Fintype.card_congr (e.subtypeEquiv hpred)

/-- If all coefficients vanish, there are no solutions with nonzero target. -/
theorem localCubicCount_zero_coefficients (F : Type*) [Field F] [Fintype F]
    (u : F) (hu : u ≠ 0) :
    localCubicCount F u (fun _ => 0) = 0 := by
  classical
  change Fintype.card {x : Fin 3 → F // ∑ i, (0 : F) * x i ^ 3 = u} = 0
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun x => ?_⟩
  have hx : (0 : F) = u := by simpa using x.2
  exact (Ne.symm hu) hx

/-- Lemma 3.2's coefficient-independent bound. The proof needs only the
elementary cubic-fiber bound and `u ≠ 0`; the prime-congruence condition used
for the character estimate is unnecessary here. -/
private theorem localCubicCount_le_three_sq_of_nonzero_coefficient
    (F : Type*) [Field F] [Fintype F] (u : F) (a : Fin 3 → F)
    (i : Fin 3) (hi : a i ≠ 0) :
    localCubicCount F u a ≤ 3 * Fintype.card F * Fintype.card F := by
  classical
  let e : F × (Fin 2 → F) ≃ (Fin 3 → F) :=
    Fin.insertNthEquiv (fun _ => F) i
  let k (y : Fin 2 → F) : F :=
    ∑ j, a (i.succAbove j) * y j ^ 3
  have hsum (p : F × (Fin 2 → F)) :
      (∑ j, a j * (e p j) ^ 3) = a i * p.1 ^ 3 + k p.2 := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [e, k]
  let S : Finset (F × (Fin 2 → F)) :=
    Finset.univ.filter fun p => (∑ j, a j * (e p j) ^ 3) = u
  have hcount : localCubicCount F u a = S.card := by
    unfold localCubicCount
    calc
      Fintype.card {x : Fin 3 → F // ∑ j, a j * x j ^ 3 = u} =
          Fintype.card {p : F × (Fin 2 → F) // ∑ j, a j * (e p j) ^ 3 = u} :=
        Fintype.card_congr ((e.subtypeEquiv (fun _ => Iff.rfl)).symm)
      _ = S.card := by
        simpa [S] using
          (Fintype.card_subtype
            (fun p : F × (Fin 2 → F) => (∑ j, a j * (e p j) ^ 3) = u))
  have hroot (y : Fin 2 → F) :
      (Finset.univ.filter fun z : F => a i * z ^ 3 + k y = u).card ≤ 3 := by
    let v : F := (u - k y) / a i
    have heq (z : F) : a i * z ^ 3 + k y = u ↔ z ^ 3 = v := by
      dsimp [v]
      constructor
      · intro hz
        apply (eq_div_iff hi).2
        calc
          z ^ 3 * a i = a i * z ^ 3 := mul_comm _ _
          _ = u - k y := eq_sub_iff_add_eq.mpr hz
      · intro hz
        have hz' : z ^ 3 * a i = u - k y := (eq_div_iff hi).1 hz
        apply eq_sub_iff_add_eq.mp
        simpa only [mul_comm] using hz'
    have hset :
        (Finset.univ.filter fun z : F => a i * z ^ 3 + k y = u) =
          (Finset.univ.filter fun z : F => z ^ 3 = v) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact heq z
    rw [hset]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
      cubicFiber_card_le_three F v
  have hfiber (y : Fin 2 → F) :
      (S.filter fun p => p.2 = y).card ≤ 3 := by
    let T : Finset F := Finset.univ.filter fun z => a i * z ^ 3 + k y = u
    calc
      (S.filter fun p => p.2 = y).card ≤ T.card := by
        apply Finset.card_le_card_of_injOn (f := Prod.fst)
        · intro p hp
          obtain ⟨hpS, hpy⟩ := Finset.mem_filter.mp hp
          have hpEq := (Finset.mem_filter.mp hpS).2
          rw [hsum p] at hpEq
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hpy] using hpEq⟩
        · intro p hp p' hp' hfst
          have hpy := (Finset.mem_filter.mp hp).2
          have hpy' := (Finset.mem_filter.mp hp').2
          exact Prod.ext hfst (hpy.trans hpy'.symm)
      _ ≤ 3 := hroot y
  have hS : S.card ≤ 3 * Fintype.card (Fin 2 → F) := by
    calc
      S.card ≤ 3 * (Finset.univ : Finset (Fin 2 → F)).card :=
        Finset.card_le_mul_card_image_of_maps_to
          (f := fun p : F × (Fin 2 → F) => p.2) (s := S) (t := Finset.univ)
          (by intro p _; exact Finset.mem_univ _) 3
          (by intro y _; exact hfiber y)
      _ = 3 * Fintype.card (Fin 2 → F) := by simp
  calc
    localCubicCount F u a = S.card := hcount
    _ ≤ 3 * Fintype.card (Fin 2 → F) := hS
    _ = 3 * Fintype.card F * Fintype.card F := by
      simp [pow_two, mul_assoc]

theorem localCubicCount_le_three_sq (F : Type*) [Field F] [Fintype F]
    (u : F) (hu : u ≠ 0) (a : Fin 3 → F) :
    localCubicCount F u a ≤ 3 * Fintype.card F * Fintype.card F := by
  classical
  by_cases h : ∃ i, a i ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact localCubicCount_le_three_sq_of_nonzero_coefficient F u a i hi
  · have ha : a = fun _ => 0 := by
      funext i
      exact not_not.mp (not_exists.mp h i)
    rw [ha, localCubicCount_zero_coefficients F u hu]
    simp

end Erdos940
