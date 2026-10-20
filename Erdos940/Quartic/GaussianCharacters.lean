import Erdos940.Statement
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Exponents in the quartic local trace

The four nonzero Fourier terms in the local quartic count are indexed by
`jᵢ ∈ {1,2,3}` with `∑ jᵢ = 0 (mod 4)`. The finite enumeration below records
the 21 tuples and the five multiplicity patterns in the local Gauss-sum
expansion of the quartic Euler majorant.
-/

namespace Erdos940.Quartic

/-- The three nontrivial exponents of a quartic character. -/
def quarticNonzeroExponents : Finset (Fin 4) :=
  Finset.univ.filter fun j => j ≠ 0

/-- On nonzero residues, an order-four character has exactly the fourth
powers as its kernel. -/
private theorem quartic_character_units_ker_eq_fourth_powers
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    χ.toUnitHom.ker =
      (powMonoidHom 4 : (ZMod q)ˣ →* (ZMod q)ˣ).range := by
  classical
  let G := (ZMod q)ˣ
  have hdiv : 4 ∣ Nat.card G := by
    have h := MulChar.orderOf_dvd_card_sub_one (ZMod q) χ
    change 4 ∣ Nat.card (ZMod q)ˣ
    rw [Nat.card_units]
    simpa only [hχ, Nat.card_eq_fintype_card] using h
  have hpowindex :
      (powMonoidHom 4 : G →* G).range.index = 4 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd]
    exact hdiv
  have hkerindex : χ.toUnitHom.ker.index = 4 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hχpow : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hχsq : χ ^ 2 ≠ 1 := by
      intro he
      have hd := orderOf_dvd_of_pow_eq_one he
      norm_num [hχ] at hd
    have hgenpow : (χ.toUnitHom g) ^ 4 = 1 := by
      apply Units.ext
      have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ (g : ZMod q)) hχpow
      simpa [MulChar.pow_apply_coe] using hv
    have hgenpow2 : (χ.toUnitHom g) ^ 2 ≠ 1 := by
      intro he
      apply hχsq
      apply (MulChar.eq_iff hg (χ ^ 2) 1).2
      have hv := congrArg Units.val he
      simpa [MulChar.pow_apply_coe] using hv
    have hgenorder : orderOf (χ.toUnitHom g) = 4 := by
      apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4) hgenpow
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
      simpa using hgenpow2
    have hrange : χ.toUnitHom.range = Subgroup.zpowers (χ.toUnitHom g) := by
      rw [MonoidHom.range_eq_map,
        ← (Subgroup.zpowers g).eq_top_iff'.mpr hg,
        MonoidHom.map_zpowers]
    rw [Subgroup.index_ker, hrange, Nat.card_zpowers, hgenorder]
  have hle : (powMonoidHom 4 : G →* G).range ≤ χ.toUnitHom.ker := by
    rintro _ ⟨x, rfl⟩
    change χ.toUnitHom (x ^ 4) = 1
    rw [map_pow]
    have hχpow : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hx := congrArg (fun φ : MulChar (ZMod q) ℂ => φ (x : ZMod q)) hχpow
    apply Units.ext
    simpa [MulChar.pow_apply_coe] using hx
  have hcardpow : Nat.card (powMonoidHom 4 : G →* G).range * 4 = Nat.card G := by
    simpa only [hpowindex] using
      (powMonoidHom 4 : G →* G).range.card_mul_index
  have hcardker : Nat.card χ.toUnitHom.ker * 4 = Nat.card G := by
    simpa only [hkerindex] using χ.toUnitHom.ker.card_mul_index
  have hcard : Nat.card χ.toUnitHom.ker ≤
      Nat.card (powMonoidHom 4 : G →* G).range := by
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

private theorem quartic_unit_fiber_card_of_exists
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (y : (ZMod q)ˣ)
    (hy : ∃ x : (ZMod q)ˣ, x ^ 4 = y) :
    Nat.card {x : (ZMod q)ˣ // x ^ 4 = y} = 4 := by
  classical
  let G := (ZMod q)ˣ
  have hdiv : 4 ∣ Nat.card G := by
    have h := MulChar.orderOf_dvd_card_sub_one (ZMod q) χ
    change 4 ∣ Nat.card (ZMod q)ˣ
    rw [Nat.card_units]
    simpa only [hχ, Nat.card_eq_fintype_card] using h
  have hker : Nat.card (powMonoidHom 4 : G →* G).ker = 4 := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right_iff_dvd]
    exact hdiv
  have hrange : y ∈ Set.range (powMonoidHom 4 : G →* G) := hy
  have hone : (1 : G) ∈ Set.range (powMonoidHom 4 : G →* G) :=
    ⟨1, by simp⟩
  have hfiber := MonoidHom.card_fiber_eq_of_mem_range
    (powMonoidHom 4 : G →* G) hrange hone
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hker_card :
      (Finset.univ.filter fun x : G => x ^ 4 = 1).card =
        Nat.card (powMonoidHom 4 : G →* G).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  simpa only [powMonoidHom_apply, hker_card, hker] using hfiber

/-- The quartic-root multiplicity identity on a prime field. -/
theorem quartic_root_count_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (y : ZMod q) :
    (Nat.card {x : ZMod q // x ^ 4 = y} : ℂ) =
      1 + χ y + (χ ^ 2) y + (χ ^ 3) y := by
  classical
  by_cases hy : y = 0
  · subst y
    have hfiber : Nat.card {x : ZMod q // x ^ 4 = 0} = 1 := by
      have hs : (Finset.univ.filter fun x : ZMod q => x ^ 4 = 0) = {0} := by
        ext x
        simp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hs]
      simp
    norm_num [hfiber, MulChar.map_zero]
  let uy : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hy).unit
  have huy : (uy : ZMod q) = y := (isUnit_iff_ne_zero.mpr hy).unit_spec
  have hcharfourth : χ y = 1 ↔ ∃ x : ZMod q, x ^ 4 = y := by
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
        uy ∈ (powMonoidHom 4 : (ZMod q)ˣ →* (ZMod q)ˣ).range ↔
          ∃ x : ZMod q, x ^ 4 = y := by
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
    rw [quartic_character_units_ker_eq_fourth_powers q χ hχ] at hker
    exact hker.symm.trans hrange
  by_cases hχy : χ y = 1
  · obtain ⟨x, hx⟩ := hcharfourth.mp hχy
    have hx0 : x ≠ 0 := by
      intro hzero
      apply hy
      simpa [hzero] using hx.symm
    let ux : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hx0).unit
    have hux : ux ^ 4 = uy := by
      apply Units.ext
      simpa [ux, huy] using hx
    have hcountunits := quartic_unit_fiber_card_of_exists q χ hχ uy ⟨ux, hux⟩
    let e : {v : (ZMod q)ˣ // v ^ 4 = uy} ≃
        {z : ZMod q // z ^ 4 = y} := {
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
    have hcount : Nat.card {z : ZMod q // z ^ 4 = y} = 4 := by
      calc
        Nat.card {z : ZMod q // z ^ 4 = y} =
            Nat.card {v : (ZMod q)ˣ // v ^ 4 = uy} := Nat.card_congr e.symm
        _ = 4 := hcountunits
    rw [hcount, hχy]
    have hχ2 : (χ ^ 2) y = 1 := by
      simp [MulChar.pow_apply' χ (by decide : 2 ≠ 0), hχy]
    have hχ3 : (χ ^ 3) y = 1 := by
      simp [MulChar.pow_apply' χ (by decide : 3 ≠ 0), hχy]
    rw [hχ2, hχ3]
    norm_num
  · have hcount : Nat.card {z : ZMod q // z ^ 4 = y} = 0 := by
      haveI : IsEmpty {z : ZMod q // z ^ 4 = y} :=
        ⟨fun z => hχy (hcharfourth.mpr ⟨z.1, z.2⟩)⟩
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero
    have hchar : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
    have hz4 : (χ y) ^ 4 = 1 := by
      have hv := congrArg (fun φ : MulChar (ZMod q) ℂ => φ y) hchar
      simpa [MulChar.pow_apply' χ (by decide : 4 ≠ 0),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)] using hv
    have hfactor : (χ y - 1) * (1 + χ y + (χ y) ^ 2 + (χ y) ^ 3) = 0 := by
      calc
        (χ y - 1) * (1 + χ y + (χ y) ^ 2 + (χ y) ^ 3) =
            (χ y) ^ 4 - 1 := by ring
        _ = 0 := by rw [hz4]; ring
    have hne : χ y - 1 ≠ 0 := sub_ne_zero.mpr hχy
    have hsum : 1 + χ y + (χ y) ^ 2 + (χ y) ^ 3 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hne
    rw [hcount, MulChar.pow_apply' χ (by decide : 2 ≠ 0),
      MulChar.pow_apply' χ (by decide : 3 ≠ 0)]
    simpa only [Nat.cast_zero] using hsum.symm

/-- The single-variable additive quartic sum becomes three Gauss sums once
the quartic character root-count identity is available. This formulation is
valid over any finite field and isolates precisely the character-theoretic
input still needed for the full local trace. -/
theorem quartic_exponential_sum_eq_gauss
    (F : Type*) [Field F] [Fintype F]
    (χ : Fin 4 → MulChar F ℂ)
    (hroot : ∀ y : F,
      (Nat.card {x : F // x ^ 4 = y} : ℂ) =
        1 + ∑ j ∈ quarticNonzeroExponents, χ j y)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (t : F) (ht : t ≠ 0) :
    (∑ x : F, ψ (t * x ^ 4)) =
      ∑ j ∈ quarticNonzeroExponents,
        (χ j)⁻¹ t * gaussSum (χ j) ψ := by
  classical
  have hfiber :
      (∑ x : F, ψ (t * x ^ 4)) =
        ∑ y : F, (Nat.card {x : F // x ^ 4 = y} : ℂ) * ψ (t * y) := by
    calc
      (∑ x : F, ψ (t * x ^ 4)) =
          ∑ y : F, ∑ x ∈ (Finset.univ.filter fun x : F => x ^ 4 = y),
            ψ (t * x ^ 4) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (x ^ 4)) _
      _ = ∑ y : F, (Nat.card {x : F // x ^ 4 = y} : ℂ) * ψ (t * y) := by
        apply Finset.sum_congr rfl
        intro y _
        calc
          (∑ x ∈ (Finset.univ.filter fun x : F => x ^ 4 = y),
              ψ (t * x ^ 4)) =
              (Finset.univ.filter fun x : F => x ^ 4 = y).card * ψ (t * y) := by
            rw [Finset.sum_congr rfl (fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
              rw [hx])]
            simp
          _ = (Nat.card {x : F // x ^ 4 = y} : ℂ) * ψ (t * y) := by
            simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hzero : (∑ y : F, ψ (t * y)) = 0 := by
    simpa [ht, mul_comm t] using AddChar.sum_mulShift t hψ
  let ut : Fˣ := (isUnit_iff_ne_zero.mpr ht).unit
  have hut : (ut : F) = t := (isUnit_iff_ne_zero.mpr ht).unit_spec
  have hshift (j : Fin 4) :
      (∑ y : F, χ j y * ψ (t * y)) =
        (χ j)⁻¹ t * gaussSum (χ j) ψ := by
    simpa only [gaussSum, AddChar.mulShift_apply, hut, mul_comm t] using
      gaussSum_mulShift_eq (χ j) ψ ut
  calc
    (∑ x : F, ψ (t * x ^ 4)) =
        ∑ y : F, (Nat.card {x : F // x ^ 4 = y} : ℂ) * ψ (t * y) := hfiber
    _ = ∑ y : F, (1 + ∑ j ∈ quarticNonzeroExponents, χ j y) * ψ (t * y) := by
      simp_rw [hroot]
    _ = ∑ j ∈ quarticNonzeroExponents,
          (χ j)⁻¹ t * gaussSum (χ j) ψ := by
      simp_rw [add_mul, one_mul, Finset.sum_mul]
      rw [Finset.sum_add_distrib, hzero]
      simp only [zero_add]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact hshift j

private theorem sum_quarticNonzeroExponents (f : Fin 4 → ℂ) :
    (∑ j ∈ quarticNonzeroExponents, f j) = f 1 + f 2 + f 3 := by
  have hs : quarticNonzeroExponents = ({1, 2, 3} : Finset (Fin 4)) := by decide
  rw [hs]
  simp [add_assoc]

/-- The quartic exponential sum is the sum of the three character Gauss
sums for every order-four character on a prime field. -/
theorem quartic_exponential_sum_eq_gauss_of_order_four
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (t : ZMod q) (ht : t ≠ 0) :
    (∑ x : ZMod q, ψ (t * x ^ 4)) =
      ∑ j ∈ quarticNonzeroExponents,
        (χ ^ (j : ℕ))⁻¹ t * gaussSum (χ ^ (j : ℕ)) ψ := by
  apply quartic_exponential_sum_eq_gauss (ZMod q)
    (fun j => χ ^ (j : ℕ)) ?_ ψ hψ t ht
  intro y
  rw [sum_quarticNonzeroExponents]
  simpa [add_assoc] using quartic_root_count_character q χ hχ y

/-- Additive orthogonality for the coefficient-weighted quartic zero count. -/
theorem quartic_zero_count_fourier
    (F : Type*) [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a : Fin 4 → F) :
    (Fintype.card F : ℂ) *
        (Nat.card {x : Fin 4 → F // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
      ∑ s : F, ∏ i : Fin 4, ∑ x : F, ψ (s * a i * x ^ 4) := by
  classical
  have horth (v : F) :
      (∑ s : F, ψ (s * v)) =
        if v = 0 then (Fintype.card F : ℂ) else 0 := by
    simpa using AddChar.sum_mulShift v hψ
  have hcount :
      (Nat.card {x : Fin 4 → F // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
        ∑ x : Fin 4 → F,
          if ∑ i, a i * x i ^ 4 = 0 then (1 : ℂ) else 0 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hphase (s : F) (x : Fin 4 → F) :
      (∏ i : Fin 4, ψ (s * a i * x i ^ 4)) =
        ψ (s * (∑ i : Fin 4, a i * x i ^ 4)) := by
    have hprod :
        (∏ i : Fin 4, ψ (s * a i * x i ^ 4)) =
          ψ (∑ i : Fin 4, s * a i * x i ^ 4) := by
      simp only [Fin.sum_univ_four, AddChar.map_add_eq_mul]
      simp [Fin.prod_univ_succ, mul_assoc]
    rw [hprod, Finset.mul_sum]
    congr 1
    simp_rw [mul_assoc]
  calc
    (Fintype.card F : ℂ) *
        (Nat.card {x : Fin 4 → F // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
          ∑ x : Fin 4 → F,
            if ∑ i, a i * x i ^ 4 = 0 then (Fintype.card F : ℂ) else 0 := by
      rw [hcount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x : Fin 4 → F,
          ∑ s : F, ψ (s * (∑ i, a i * x i ^ 4)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (horth _).symm
    _ = ∑ s : F, ∏ i : Fin 4, ∑ x : F, ψ (s * a i * x ^ 4) := by
      rw [Finset.sum_comm]
      simp_rw [← hphase]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.prod_sum]

/-- Before summing over the nonzero additive frequencies, the split-prime
zero count is a product of three Gauss terms in each of four coordinates.
Character orthogonality later removes exactly the tuples outside
`quarticExponents`. -/
theorem quartic_zero_count_gauss_pretrace
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    (q : ℂ) *
        (Nat.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
      (q : ℂ) ^ 4 +
        ∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ∏ i : Fin 4,
            ∑ j ∈ quarticNonzeroExponents,
              (χ ^ (j : ℕ))⁻¹ (s * a i) *
                gaussSum (χ ^ (j : ℕ)) ψ := by
  classical
  have hfourier := quartic_zero_count_fourier (ZMod q) ψ hψ a
  rw [ZMod.card] at hfourier
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
    (f := fun s => ∏ i : Fin 4, ∑ x : ZMod q, ψ (s * a i * x ^ 4))
    (Finset.mem_univ 0)
  rw [← hsplit] at hfourier
  have hzero :
      (∏ i : Fin 4, ∑ x : ZMod q, ψ ((0 : ZMod q) * a i * x ^ 4)) =
        (q : ℂ) ^ 4 := by
    simp [ZMod.card, Finset.prod_const]
  rw [hzero] at hfourier
  calc
    (q : ℂ) *
        (Nat.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
        ∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ∏ i : Fin 4, ∑ x : ZMod q, ψ (s * a i * x ^ 4) + (q : ℂ) ^ 4 := hfourier
    _ = (q : ℂ) ^ 4 +
        ∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ∏ i : Fin 4,
            ∑ j ∈ quarticNonzeroExponents,
              (χ ^ (j : ℕ))⁻¹ (s * a i) *
                gaussSum (χ ^ (j : ℕ)) ψ := by
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
      apply Finset.prod_congr rfl
      intro i _
      exact quartic_exponential_sum_eq_gauss_of_order_four q χ hχ ψ hψ
        (s * a i) (mul_ne_zero hs0 (ha i))

/-- The frequency sum of a power of an order-four character vanishes unless
the exponent is divisible by four. This is the selection rule behind the
21 surviving terms. -/
theorem quartic_character_power_sum
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (k : ℕ) :
    (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0, (χ ^ k) s) =
      if 4 ∣ k then (Fintype.card (ZMod q)ˣ : ℂ) else 0 := by
  classical
  have hsum :
      (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0, (χ ^ k) s) =
        ∑ s : ZMod q, (χ ^ k) s := by
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
      (f := fun s => (χ ^ k) s) (Finset.mem_univ 0)
    simpa [MulChar.map_zero] using hsplit
  rw [hsum]
  have hpow : χ ^ k = 1 ↔ 4 ∣ k := by
    rw [← hχ, orderOf_dvd_iff_pow_eq_one]
  by_cases hk : 4 ∣ k
  · simp [hk, hpow.mpr hk, MulChar.sum_one_eq_card_units]
  · simpa [hk] using MulChar.sum_eq_zero_of_ne_one (fun he => hk (hpow.mp he))

/-- The product of character factors in a four-coordinate term depends on
the frequency through the sum of its exponents. -/
theorem quartic_character_frequency_product
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (j : Fin 4 → Fin 4) (s : ZMod q) :
    (∏ i : Fin 4, (χ ^ (j i : ℕ))⁻¹ s) =
      (χ ^ (∑ i : Fin 4, (j i : ℕ)))⁻¹ s := by
  by_cases hs : s = 0
  · subst s
    simp [MulChar.map_zero]
  let us : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hs).unit
  have hus : (us : ZMod q) = s := (isUnit_iff_ne_zero.mpr hs).unit_spec
  have hpow (k : ℕ) : (χ ^ k) s = (χ s) ^ k := by
    simpa only [hus] using MulChar.pow_apply_coe χ k us
  simp_rw [MulChar.inv_apply_eq_inv', hpow]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]

/-- Exponent vectors appearing in the nonzero-frequency quartic trace. -/
def quarticExponents : Finset (Fin 4 → Fin 4) :=
  Finset.univ.filter fun j => (∀ i, j i ≠ 0) ∧ (∑ i, (j i).val) % 4 = 0

/-- All 81 nonzero quartic exponent vectors, before character
orthogonality imposes the congruence condition. -/
def quarticNonzeroTuples : Finset (Fin 4 → Fin 4) :=
  Finset.univ.filter fun j => ∀ i, j i ≠ 0

/-- Summing the frequency factor of a nonzero exponent vector retains
exactly the 21 vectors in `quarticExponents`. -/
theorem quartic_frequency_selector
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (j : Fin 4 → Fin 4)
    (hj : ∀ i, j i ≠ 0) :
    (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ∏ i : Fin 4, (χ ^ (j i : ℕ))⁻¹ s) =
        if j ∈ quarticExponents then (Fintype.card (ZMod q)ˣ : ℂ) else 0 := by
  classical
  simp_rw [quartic_character_frequency_product q χ j]
  have horder : orderOf χ⁻¹ = 4 := by simpa [hχ] using orderOf_inv χ
  rw [← inv_pow, quartic_character_power_sum q χ⁻¹ horder]
  have hmem : j ∈ quarticExponents ↔ 4 ∣ ∑ i : Fin 4, (j i : ℕ) := by
    simp [quarticExponents, hj, Nat.dvd_iff_mod_eq_zero]
  simp only [hmem]

/-- The product of four three-term sums is the sum over all 81 nonzero
exponent vectors. -/
theorem quartic_product_sum_expansion (f : Fin 4 → Fin 4 → ℂ) :
    (∏ i : Fin 4, ∑ j ∈ quarticNonzeroExponents, f i j) =
      ∑ J ∈ quarticNonzeroTuples,
        ∏ i : Fin 4, f i (J i) := by
  classical
  unfold quarticNonzeroTuples
  have hsingle (i : Fin 4) :
      (∑ j ∈ quarticNonzeroExponents, f i j) =
        ∑ j : Fin 4, if j ≠ 0 then f i j else 0 := by
    simp [quarticNonzeroExponents, Finset.sum_filter]
  simp_rw [hsingle]
  rw [Fintype.prod_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hJ : ∀ i, J i ≠ 0
  · simp [hJ]
  · obtain ⟨i, hi⟩ := not_forall.mp hJ
    have hi0 : J i = 0 := not_ne_iff.mp hi
    have hz : (∏ k : Fin 4, if J k = 0 then 0 else f k (J k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi0])
    simpa [hJ] using hz

/-- The frequency sum removes all 60 noninvariant vectors from the
81-term product expansion, leaving the 21-term trace. -/
theorem quartic_frequency_weighted_trace
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (w : (Fin 4 → Fin 4) → ℂ) :
    (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ∑ J ∈ quarticNonzeroTuples,
        (∏ i : Fin 4, (χ ^ (J i : ℕ))⁻¹ s) * w J) =
      (Fintype.card (ZMod q)ˣ : ℂ) *
        ∑ J ∈ quarticExponents, w J := by
  classical
  have hfilter :
      quarticNonzeroTuples.filter (fun J => J ∈ quarticExponents) =
        quarticExponents := by
    ext J
    simp [quarticNonzeroTuples, quarticExponents]
  calc
    (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ∑ J ∈ quarticNonzeroTuples,
        (∏ i : Fin 4, (χ ^ (J i : ℕ))⁻¹ s) * w J) =
        ∑ J ∈ quarticNonzeroTuples,
          (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
            ∏ i : Fin 4, (χ ^ (J i : ℕ))⁻¹ s) * w J := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = ∑ J ∈ quarticNonzeroTuples,
          (if J ∈ quarticExponents then (Fintype.card (ZMod q)ˣ : ℂ) else 0) *
            w J := by
      apply Finset.sum_congr rfl
      intro J hJ
      have hnonzero : ∀ i, J i ≠ 0 :=
        (Finset.mem_filter.mp hJ).2
      rw [quartic_frequency_selector q χ hχ J hnonzero]
    _ = (Fintype.card (ZMod q)ˣ : ℂ) *
          ∑ J ∈ quarticExponents, w J := by
      simp only [ite_mul, zero_mul]
      rw [← Finset.sum_filter, hfilter, Finset.mul_sum]

/-- Exact 21-term quartic Gauss trace for a unit-coefficient diagonal form
at a split prime. The Gauss sum uses `ψ`, and no Jacobi-sum evaluation is
needed for this identity. -/
theorem quartic_zero_count_gauss_trace
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    (q : ℂ) *
        (Nat.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
      (q : ℂ) ^ 4 + (Fintype.card (ZMod q)ˣ : ℂ) *
        ∑ J ∈ quarticExponents,
          ∏ i : Fin 4,
            (χ ^ (J i : ℕ))⁻¹ (a i) * gaussSum (χ ^ (J i : ℕ)) ψ := by
  rw [quartic_zero_count_gauss_pretrace q χ hχ ψ hψ a ha]
  congr 1
  calc
    (∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ∏ i : Fin 4,
        ∑ j ∈ quarticNonzeroExponents,
          (χ ^ (j : ℕ))⁻¹ (s * a i) * gaussSum (χ ^ (j : ℕ)) ψ) =
        ∑ s ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ∑ J ∈ quarticNonzeroTuples,
            (∏ i : Fin 4, (χ ^ (J i : ℕ))⁻¹ s) *
              ∏ i : Fin 4,
                (χ ^ (J i : ℕ))⁻¹ (a i) * gaussSum (χ ^ (J i : ℕ)) ψ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [quartic_product_sum_expansion]
      apply Finset.sum_congr rfl
      intro J _
      simp_rw [map_mul, mul_assoc]
      rw [Finset.prod_mul_distrib]
    _ = (Fintype.card (ZMod q)ˣ : ℂ) *
          ∑ J ∈ quarticExponents,
            ∏ i : Fin 4,
              (χ ^ (J i : ℕ))⁻¹ (a i) * gaussSum (χ ^ (J i : ℕ)) ψ :=
      quartic_frequency_weighted_trace q χ hχ _

/-- In a prime field, the scalar in the trace formula is exactly `q - 1`. -/
theorem quartic_zero_count_gauss_trace_q_sub_one
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    (q : ℂ) *
        (Nat.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 4 = 0} : ℂ) =
      (q : ℂ) ^ 4 + ((q - 1 : ℕ) : ℂ) *
        ∑ J ∈ quarticExponents,
          ∏ i : Fin 4,
            (χ ^ (J i : ℕ))⁻¹ (a i) * gaussSum (χ ^ (J i : ℕ)) ψ := by
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units,
      Nat.card_eq_fintype_card, ZMod.card]
  simpa [hcard] using quartic_zero_count_gauss_trace q χ hχ ψ hψ a ha

/-- The quadratic Gauss sum inside an order-four character has square `q`. -/
theorem quartic_gauss_two_sq
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) :
    gaussSum (χ ^ 2) ψ ^ 2 = (q : ℂ) := by
  have hχ2ne : χ ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [hχ] at hd
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hquad : (χ ^ 2).IsQuadratic :=
    MulChar.isQuadratic_iff_sq_eq_one.mpr (by simpa [← pow_mul] using hχ4)
  have hneg : (χ ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' χ (by decide : 2 ≠ 0)]
    calc
      χ (-1) ^ 2 = χ ((-1 : ZMod q) ^ 2) := (map_pow χ (-1) 2).symm
      _ = 1 := by simp
  simpa [hneg, ZMod.card] using gaussSum_sq hχ2ne hquad hψ

/-- The first and third quartic Gauss sums multiply to `χ(-1)q`. -/
theorem quartic_gauss_one_mul_three
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ 3) ψ = χ (-1) * (q : ℂ) := by
  have hχne : χ ≠ 1 := by
    intro he
    simp [he] at hχ
  simpa [hχ, ZMod.card] using
    gaussSum_mul_gaussSum_pow_orderOf_sub_one hχne hψ

/-- The first quartic Gauss sum squared factors through the quadratic
Gauss sum and the Jacobi sum `J(χ,χ)`. -/
theorem quartic_gauss_one_sq_eq_jacobi
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ) :
    gaussSum χ ψ ^ 2 = gaussSum (χ ^ 2) ψ * jacobiSum χ χ := by
  have hχ2ne : χ ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [hχ] at hd
  simpa [pow_two] using
    (jacobiSum_mul_nontrivial (χ := χ) (φ := χ)
      (by simpa [pow_two] using hχ2ne) ψ).symm

/-- The normalized fourth Gauss power is the Jacobi-square ratio used in
the CM constituent of the local trace. -/
theorem quartic_gauss_fourth_div_sq_eq_jacobi_sq_div
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 4 / (q : ℂ) ^ 2 = jacobiSum χ χ ^ 2 / (q : ℂ) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hJ := quartic_gauss_one_sq_eq_jacobi q χ hχ ψ
  have hG2 := quartic_gauss_two_sq q χ hχ ψ hψ
  have hfourth : gaussSum χ ψ ^ 4 = (q : ℂ) * jacobiSum χ χ ^ 2 := by
    calc
      gaussSum χ ψ ^ 4 = (gaussSum χ ψ ^ 2) ^ 2 := by ring
      _ = (gaussSum (χ ^ 2) ψ * jacobiSum χ χ) ^ 2 := by rw [hJ]
      _ = (q : ℂ) * jacobiSum χ χ ^ 2 := by rw [mul_pow, hG2]
  rw [hfourth]
  field_simp

/-- One normalized summand of the 21-term local trace. -/
noncomputable def quarticGaussTerm
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ) (ψ : AddChar (ZMod q) ℂ)
    (a : Fin 4 → ZMod q) (J : Fin 4 → Fin 4) : ℂ :=
  (∏ i : Fin 4,
    (χ ^ (J i : ℕ))⁻¹ (a i) * gaussSum (χ ^ (J i : ℕ)) ψ) / (q : ℂ) ^ 2

/-- The `(2,2,2,2)` summand is the quadratic character of the product of
coefficients. -/
theorem quarticGaussTerm_all_two
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) :
    quarticGaussTerm q χ ψ a (fun _ => 2) = (χ ^ 2) (∏ i, a i) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hquad : (χ ^ 2).IsQuadratic :=
    MulChar.isQuadratic_iff_sq_eq_one.mpr (by simpa [← pow_mul] using hχ4)
  have hτ := quartic_gauss_two_sq q χ hχ ψ hψ
  have htwo : ((2 : Fin 4) : ℕ) = 2 := rfl
  unfold quarticGaussTerm
  simp only [htwo, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
  rw [hquad.inv]
  rw [← map_prod]
  have hτ4 : gaussSum (χ ^ 2) ψ ^ 4 = (q : ℂ) ^ 2 := by
    calc
      gaussSum (χ ^ 2) ψ ^ 4 = (gaussSum (χ ^ 2) ψ ^ 2) ^ 2 := by ring
      _ = (q : ℂ) ^ 2 := by rw [hτ]
  rw [hτ4]
  field_simp

/-- The `(1,1,1,1)` summand is the CM Jacobi-square factor twisted by
the inverse quartic character of the coefficient product. -/
theorem quarticGaussTerm_all_one
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) :
    quarticGaussTerm q χ ψ a (fun _ => 1) =
      χ⁻¹ (∏ i, a i) * (jacobiSum χ χ ^ 2 / (q : ℂ)) := by
  unfold quarticGaussTerm
  have hone : ((1 : Fin 4) : ℕ) = 1 := rfl
  simp only [hone, pow_one, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_fin]
  rw [← map_prod]
  rw [mul_div_assoc,
    quartic_gauss_fourth_div_sq_eq_jacobi_sq_div q χ hχ ψ hψ]

private theorem quartic_prod_fin_four (f : Fin 4 → ℂ) :
    (∏ i : Fin 4, f i) = f 0 * f 1 * f 2 * f 3 := by
  simp [Fin.prod_univ_succ, mul_assoc]

/-- A representative `(1,1,3,3)` exponent vector. -/
def quarticPairExponent : Fin 4 → Fin 4 :=
  fun i => if (i : ℕ) < 2 then 1 else 3

/-- A complementary-pair trace summand is a quartic residue value. -/
theorem quarticGaussTerm_pair_canonical
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) :
    quarticGaussTerm q χ ψ a quarticPairExponent =
      χ (a 0 ^ 3 * a 1 ^ 3 * a 2 * a 3) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hτ := quartic_gauss_one_mul_three q χ hχ ψ hψ
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχinv : χ⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    calc χ * χ ^ 3 = χ ^ 4 := by group
      _ = 1 := hχ4
  have hχ3inv : (χ ^ 3)⁻¹ = χ := by rw [← hχinv]; simp
  have hχneg : χ (-1) ^ 2 = 1 := by
    calc
      χ (-1) ^ 2 = χ ((-1 : ZMod q) ^ 2) := (map_pow χ (-1) 2).symm
      _ = 1 := by simp
  unfold quarticGaussTerm
  rw [quartic_prod_fin_four]
  simp only [quarticPairExponent, Fin.val_zero, Fin.val_one,
    show ((2 : Fin 4) : ℕ) = 2 by rfl,
    show ((3 : Fin 4) : ℕ) = 3 by rfl,
    Nat.reduceLT, ite_true, ite_false, pow_one]
  rw [hχinv, hχ3inv]
  simp only [MulChar.pow_apply' χ (by decide : 3 ≠ 0)]
  rw [show χ (a 0) ^ 3 * gaussSum χ ψ *
      (χ (a 1) ^ 3 * gaussSum χ ψ) *
      (χ (a 2) * gaussSum (χ ^ 3) ψ) *
      (χ (a 3) * gaussSum (χ ^ 3) ψ) =
      χ (a 0 ^ 3 * a 1 ^ 3 * a 2 * a 3) *
        (gaussSum χ ψ * gaussSum (χ ^ 3) ψ) ^ 2 by
          simp [map_mul, map_pow]
          ring]
  rw [hτ, mul_pow, hχneg, one_mul]
  field_simp

/-- A representative `(1,3,2,2)` exponent vector. -/
def quarticMixedExponent : Fin 4 → Fin 4 :=
  fun i => if i = 0 then 1 else if i = 1 then 3 else 2

/-- A mixed trace summand is the quartic residue value of a negative
coefficient radicand. -/
theorem quarticGaussTerm_mixed_canonical
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) :
    quarticGaussTerm q χ ψ a quarticMixedExponent =
      χ (-(a 0 ^ 3 * a 1 * a 2 ^ 2 * a 3 ^ 2)) := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hτ13 := quartic_gauss_one_mul_three q χ hχ ψ hψ
  have hτ2 := quartic_gauss_two_sq q χ hχ ψ hψ
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχinv : χ⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    calc χ * χ ^ 3 = χ ^ 4 := by group
      _ = 1 := hχ4
  have hχ3inv : (χ ^ 3)⁻¹ = χ := by rw [← hχinv]; simp
  have hχ2inv : (χ ^ 2)⁻¹ = χ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc (χ ^ 2) * (χ ^ 2) = χ ^ 4 := by group
      _ = 1 := hχ4
  unfold quarticGaussTerm
  rw [quartic_prod_fin_four]
  simp only [quarticMixedExponent]
  norm_num
  rw [hχinv, hχ3inv, hχ2inv]
  simp only [MulChar.pow_apply' χ (by decide : 3 ≠ 0),
    MulChar.pow_apply' χ (by decide : 2 ≠ 0)]
  rw [show χ (a 0) ^ 3 * gaussSum χ ψ *
      (χ (a 1) * gaussSum (χ ^ 3) ψ) *
      (χ (a 2) ^ 2 * gaussSum (χ ^ 2) ψ) *
      (χ (a 3) ^ 2 * gaussSum (χ ^ 2) ψ) =
      χ (a 0 ^ 3 * a 1 * a 2 ^ 2 * a 3 ^ 2) *
        (gaussSum χ ψ * gaussSum (χ ^ 3) ψ) *
        gaussSum (χ ^ 2) ψ ^ 2 by
          simp [map_mul, map_pow]
          ring]
  rw [hτ13, hτ2]
  rw [show χ (-(a 0 ^ 3 * a 1 * a 2 ^ 2 * a 3 ^ 2)) =
      χ (a 0 ^ 3 * a 1 * a 2 ^ 2 * a 3 ^ 2) * χ (-1) by
        rw [neg_eq_neg_one_mul, map_mul, mul_comm]]
  field_simp

/-- The `(3,3,3,3)` term is the conjugate CM Jacobi-square factor twisted
by the quartic character of the coefficient product. -/
theorem quarticGaussTerm_all_three
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) :
    quarticGaussTerm q χ ψ a (fun _ => 3) =
      χ (∏ i, a i) * (jacobiSum χ⁻¹ χ⁻¹ ^ 2 / (q : ℂ)) := by
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχinv : χ⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    calc χ * χ ^ 3 = χ ^ 4 := by group
      _ = 1 := hχ4
  have hχ3 : orderOf (χ ^ 3) = 4 := by
    rw [← hχinv]
    simpa [hχ] using orderOf_inv χ
  have hχ3inv : (χ ^ 3)⁻¹ = χ := by rw [← hχinv]; simp
  have hterm : quarticGaussTerm q χ ψ a (fun _ => 3) =
      quarticGaussTerm q (χ ^ 3) ψ a (fun _ => 1) := by
    unfold quarticGaussTerm
    simp
  rw [hterm, quarticGaussTerm_all_one q (χ ^ 3) hχ3 ψ hψ a,
    hχ3inv, ← hχinv]

/-- The quartic Jacobi sum is a Gaussian integer, represented inside `ℂ`
as an element of `ℤ[I]`. -/
theorem quartic_jacobi_mem_gaussian_subalgebra
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    jacobiSum χ χ ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) := by
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  exact jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ4 hχ4
    Complex.isPrimitiveRoot_I

/-- A concrete Gaussian-integer lift of the quartic Jacobi sum. -/
theorem quartic_jacobi_exists_gaussianInt
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    ∃ J : GaussianInt, (J : ℂ) = jacobiSum χ χ := by
  have hLift (z : ℂ) (hz : z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ)) :
      ∃ J : GaussianInt, (J : ℂ) = z := by
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      have hz' : z = Complex.I := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨0, 1⟩, by simp [GaussianInt.toComplex_def]⟩
    | algebraMap r =>
      exact ⟨(r : GaussianInt), by simp⟩
    | add x y hx hy ex ey =>
      obtain ⟨gx, hgx⟩ := ex
      obtain ⟨gy, hgy⟩ := ey
      exact ⟨gx + gy, by simp [hgx, hgy]⟩
    | mul x y hx hy ex ey =>
      obtain ⟨gx, hgx⟩ := ex
      obtain ⟨gy, hgy⟩ := ey
      exact ⟨gx * gy, by simp [hgx, hgy]⟩
  exact hLift _ (quartic_jacobi_mem_gaussian_subalgebra q χ hχ)

/-- The inverse-character Jacobi sum is the complex conjugate of the
original quartic Jacobi sum. -/
theorem quartic_jacobi_conj
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    star (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
  simp only [jacobiSum, star_sum, star_mul, MulChar.star_apply']
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The Jacobi sum and its inverse-character partner multiply to the
underlying prime. This is the norm identity before identifying conjugation
in the Gaussian integers. -/
theorem quartic_jacobi_mul_inverse_jacobi
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = (q : ℂ) := by
  have hχne : χ ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hχ
    norm_num at hχ
  have hχsq : χ * χ ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using he : χ ^ 2 = 1)
    norm_num [hχ] at hd
  have hchar : ringChar ℂ ≠ ringChar (ZMod q) := by
    simpa [ZMod.ringChar_zmod_n] using
      (Fact.out : q.Prime).ne_zero.symm
  simpa [ZMod.card] using
    (jacobiSum_mul_jacobiSum_inv hchar hχne hχne hχsq)

/-- The quartic Jacobi sum has a Gaussian-integer representative of norm `q`. -/
theorem quartic_jacobi_exists_gaussianInt_norm
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) :
    ∃ J : GaussianInt, (J : ℂ) = jacobiSum χ χ ∧ J.norm = (q : ℤ) := by
  obtain ⟨J, hJ⟩ := quartic_jacobi_exists_gaussianInt q χ hχ
  refine ⟨J, hJ, ?_⟩
  have hnormC : (J.norm : ℂ) = (q : ℂ) := by
    rw [GaussianInt.intCast_complex_norm, Complex.normSq_eq_conj_mul_self]
    change star (J : ℂ) * (J : ℂ) = (q : ℂ)
    rw [hJ, quartic_jacobi_conj q χ hχ, mul_comm]
    exact quartic_jacobi_mul_inverse_jacobi q χ hχ
  exact_mod_cast hnormC

/-- Number of coordinates of an exponent vector equal to `k`. -/
def exponentMultiplicity (j : Fin 4 → Fin 4) (k : Fin 4) : ℕ :=
  (Finset.univ.filter fun i => j i = k).card

/-- The five possible multiplicity patterns, in the order
`(2,2,2,2)`, `(1,1,3,3)`, `(1,3,2,2)`, `(1,1,1,1)`, `(3,3,3,3)`. -/
def quarticPattern (j : Fin 4 → Fin 4) : Prop :=
  (exponentMultiplicity j 1 = 0 ∧ exponentMultiplicity j 2 = 4 ∧
    exponentMultiplicity j 3 = 0) ∨
  (exponentMultiplicity j 1 = 2 ∧ exponentMultiplicity j 2 = 0 ∧
    exponentMultiplicity j 3 = 2) ∨
  (exponentMultiplicity j 1 = 1 ∧ exponentMultiplicity j 2 = 2 ∧
    exponentMultiplicity j 3 = 1) ∨
  (exponentMultiplicity j 1 = 4 ∧ exponentMultiplicity j 2 = 0 ∧
    exponentMultiplicity j 3 = 0) ∨
  (exponentMultiplicity j 1 = 0 ∧ exponentMultiplicity j 2 = 0 ∧
    exponentMultiplicity j 3 = 4)

instance quarticPattern_decidable : DecidablePred quarticPattern := fun k => by
  unfold quarticPattern
  infer_instance

set_option maxRecDepth 4096 in
theorem mem_quarticExponents_iff_pattern (j : Fin 4 → Fin 4) :
    j ∈ quarticExponents ↔ quarticPattern j := by
  have h : ∀ k : Fin 4 → Fin 4,
      k ∈ quarticExponents ↔ quarticPattern k := by decide
  exact h j

theorem quarticExponents_card : quarticExponents.card = 21 := by
  decide

theorem all_two_count :
    (quarticExponents.filter fun j => exponentMultiplicity j 2 = 4).card = 1 := by
  decide

theorem two_one_two_three_count :
    (quarticExponents.filter fun j => exponentMultiplicity j 1 = 2).card = 6 := by
  decide

theorem one_one_two_two_one_three_count :
    (quarticExponents.filter fun j => exponentMultiplicity j 1 = 1).card = 12 := by
  decide

theorem all_one_count :
    (quarticExponents.filter fun j => exponentMultiplicity j 1 = 4).card = 1 := by
  decide

theorem all_three_count :
    (quarticExponents.filter fun j => exponentMultiplicity j 3 = 4).card = 1 := by
  decide

set_option maxRecDepth 4096 in
/-- Each complementary-pair exponent pattern is a permutation of the
canonical `(1,1,3,3)` pattern. -/
theorem pair_exponent_exists_permutation (j : Fin 4 → Fin 4)
    (h1 : exponentMultiplicity j 1 = 2)
    (h2 : exponentMultiplicity j 2 = 0)
    (h3 : exponentMultiplicity j 3 = 2) :
    ∃ σ : Equiv.Perm (Fin 4),
      j = fun i => quarticPairExponent (σ i) := by
  have h : ∀ k : Fin 4 → Fin 4,
      exponentMultiplicity k 1 = 2 →
      exponentMultiplicity k 2 = 0 →
      exponentMultiplicity k 3 = 2 →
      ∃ σ : Equiv.Perm (Fin 4),
        k = fun i => quarticPairExponent (σ i) := by decide
  exact h j h1 h2 h3

set_option maxRecDepth 4096 in
/-- Each mixed exponent pattern is a permutation of the canonical
`(1,3,2,2)` pattern. -/
theorem mixed_exponent_exists_permutation (j : Fin 4 → Fin 4)
    (h1 : exponentMultiplicity j 1 = 1)
    (h2 : exponentMultiplicity j 2 = 2)
    (h3 : exponentMultiplicity j 3 = 1) :
    ∃ σ : Equiv.Perm (Fin 4),
      j = fun i => quarticMixedExponent (σ i) := by
  have h : ∀ k : Fin 4 → Fin 4,
      exponentMultiplicity k 1 = 1 →
      exponentMultiplicity k 2 = 2 →
      exponentMultiplicity k 3 = 1 →
      ∃ σ : Equiv.Perm (Fin 4),
        k = fun i => quarticMixedExponent (σ i) := by decide
  exact h j h1 h2 h3

/-- Reindexing a trace summand permutes its coefficient tuple in the
opposite direction. -/
theorem quarticGaussTerm_permutation
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ) (ψ : AddChar (ZMod q) ℂ)
    (a : Fin 4 → ZMod q) (j : Fin 4 → Fin 4)
    (σ : Equiv.Perm (Fin 4)) :
    quarticGaussTerm q χ ψ a (fun i => j (σ i)) =
      quarticGaussTerm q χ ψ (fun i => a (σ.symm i)) j := by
  unfold quarticGaussTerm
  congr 1
  simpa only [σ.symm_apply_apply] using
    (Equiv.prod_comp σ (fun k : Fin 4 =>
      (χ ^ (j k : ℕ))⁻¹ (a (σ.symm k)) *
        gaussSum (χ ^ (j k : ℕ)) ψ))

/-- All six complementary-pair trace terms have the quartic-radical form
of the canonical representative, up to a coordinate permutation. -/
theorem quarticGaussTerm_pair_of_pattern
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (j : Fin 4 → Fin 4)
    (h1 : exponentMultiplicity j 1 = 2)
    (h2 : exponentMultiplicity j 2 = 0)
    (h3 : exponentMultiplicity j 3 = 2) :
    ∃ σ : Equiv.Perm (Fin 4),
      quarticGaussTerm q χ ψ a j =
        χ (a (σ.symm 0) ^ 3 * a (σ.symm 1) ^ 3 *
          a (σ.symm 2) * a (σ.symm 3)) := by
  obtain ⟨σ, rfl⟩ := pair_exponent_exists_permutation j h1 h2 h3
  refine ⟨σ, ?_⟩
  rw [quarticGaussTerm_permutation,
    quarticGaussTerm_pair_canonical q χ hχ ψ hψ]

/-- All twelve mixed trace terms have the negative quartic-radical form
of the canonical representative, up to a coordinate permutation. -/
theorem quarticGaussTerm_mixed_of_pattern
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (j : Fin 4 → Fin 4)
    (h1 : exponentMultiplicity j 1 = 1)
    (h2 : exponentMultiplicity j 2 = 2)
    (h3 : exponentMultiplicity j 3 = 1) :
    ∃ σ : Equiv.Perm (Fin 4),
      quarticGaussTerm q χ ψ a j =
        χ (-(a (σ.symm 0) ^ 3 * a (σ.symm 1) *
          a (σ.symm 2) ^ 2 * a (σ.symm 3) ^ 2)) := by
  obtain ⟨σ, rfl⟩ := mixed_exponent_exists_permutation j h1 h2 h3
  refine ⟨σ, ?_⟩
  rw [quarticGaussTerm_permutation,
    quarticGaussTerm_mixed_canonical q χ hχ ψ hψ]

/-- Any sum of 21 terms of norm at most one has norm at most 21. Applied to
the normalized Gauss terms, this is the local bound `|Aₚ(d)| ≤ 21`. -/
theorem quarticTrace_norm_le_21 (term : (Fin 4 → Fin 4) → ℂ)
    (hterm : ∀ j ∈ quarticExponents, ‖term j‖ ≤ 1) :
    ‖∑ j ∈ quarticExponents, term j‖ ≤ 21 := by
  calc
    ‖∑ j ∈ quarticExponents, term j‖ ≤
        ∑ j ∈ quarticExponents, ‖term j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ quarticExponents, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hterm j hj
    _ = 21 := by simp [quarticExponents_card]

/-- The rational radical of a coefficient tuple in the complementary-pair
constituents. The exponents are three on `S` and one off `S`. -/
def complementaryRadicand (d : Fin 4 → ℚ) (S : Finset (Fin 4)) : ℚ :=
  ∏ i, if i ∈ S then (d i) ^ 3 else d i

/-- Its squareclass is the squareclass of the full coefficient product. -/
theorem complementaryRadicand_eq_product_mul_square
    (d : Fin 4 → ℚ) (S : Finset (Fin 4)) :
    complementaryRadicand d S =
      (∏ i, d i) * (∏ i ∈ S, d i) ^ 2 := by
  classical
  calc
    complementaryRadicand d S =
        ∏ i, d i * (if i ∈ S then d i ^ 2 else 1) := by
      unfold complementaryRadicand
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> ring
    _ = (∏ i, d i) * (∏ i ∈ S, d i) ^ 2 := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_pow]
      simp

/-- Under a nonsquare coefficient product, no complementary-pair radicand
is a rational fourth power. This applies to all three pair classes. -/
theorem complementaryRadicand_not_fourth_power
    (d : Fin 4 → ℚ) (S : Finset (Fin 4))
    (hD : ¬ IsSquare (∏ i, d i))
    (hd : ∀ i, d i ≠ 0) :
    ¬ ∃ x : ℚ, x ^ 4 = complementaryRadicand d S := by
  rintro ⟨x, hx⟩
  have hR : IsSquare (complementaryRadicand d S) :=
    ⟨x ^ 2, by calc
      complementaryRadicand d S = x ^ 4 := hx.symm
      _ = x ^ 2 * x ^ 2 := by ring⟩
  have hS : IsSquare ((∏ i ∈ S, d i) ^ 2) := ⟨∏ i ∈ S, d i, by ring⟩
  have hSne : (∏ i ∈ S, d i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hd i
  apply hD
  have hquot : IsSquare (complementaryRadicand d S / (∏ i ∈ S, d i) ^ 2) :=
    hR.div hS
  rwa [complementaryRadicand_eq_product_mul_square,
    mul_div_cancel_right₀ _ (pow_ne_zero 2 hSne)] at hquot

/-- Real part of the fourth power of a rational Gaussian number `a + bi`. -/
def gaussianFourthReal (a b : ℚ) : ℚ := a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4

/-- Imaginary part of the fourth power of a rational Gaussian number `a + bi`. -/
def gaussianFourthImag (a b : ℚ) : ℚ := 4 * a * b * (a ^ 2 - b ^ 2)

/-- A negative rational number is a Gaussian-rational fourth power exactly
when its absolute value is four times a rational fourth power. -/
theorem negative_gaussian_fourth_power_iff (R : ℚ) (hR : 0 < R) :
    (∃ a b : ℚ, gaussianFourthReal a b = -R ∧ gaussianFourthImag a b = 0) ↔
      ∃ t : ℚ, R = 4 * t ^ 4 := by
  constructor
  · rintro ⟨a, b, hreal, himag⟩
    dsimp [gaussianFourthImag] at himag
    have ha : a ≠ 0 := by
      intro ha
      simp [gaussianFourthReal, ha] at hreal
      nlinarith [sq_nonneg (b ^ 2)]
    have hb : b ≠ 0 := by
      intro hb
      simp [gaussianFourthReal, hb] at hreal
      nlinarith [sq_nonneg (a ^ 2)]
    have heq : a ^ 2 = b ^ 2 := by
      have hprod : a * b * (a ^ 2 - b ^ 2) = 0 := by
        nlinarith [himag]
      rcases mul_eq_zero.mp hprod with hab | hsq
      · rcases mul_eq_zero.mp hab with ha0 | hb0
        · exact (ha ha0).elim
        · exact (hb hb0).elim
      · exact sub_eq_zero.mp hsq
    refine ⟨a, ?_⟩
    dsimp [gaussianFourthReal] at hreal
    nlinarith [congrArg (fun z : ℚ => z ^ 2) heq]
  · rintro ⟨t, ht⟩
    refine ⟨t, t, ?_, ?_⟩
    · simp [gaussianFourthReal, ht]
      ring
    · simp [gaussianFourthImag]

/-- A positive rational Gaussian fourth power is already a rational fourth
power. The other real branch has negative sign. -/
theorem positive_gaussian_fourth_power_iff (R : ℚ) (hR : 0 < R) :
    (∃ a b : ℚ, gaussianFourthReal a b = R ∧ gaussianFourthImag a b = 0) ↔
      ∃ t : ℚ, R = t ^ 4 := by
  constructor
  · rintro ⟨a, b, hreal, himag⟩
    dsimp [gaussianFourthImag] at himag
    by_cases ha : a = 0
    · refine ⟨b, ?_⟩
      simpa [gaussianFourthReal, ha] using hreal.symm
    by_cases hb : b = 0
    · refine ⟨a, ?_⟩
      simpa [gaussianFourthReal, hb] using hreal.symm
    have heq : a ^ 2 = b ^ 2 := by
      have hprod : a * b * (a ^ 2 - b ^ 2) = 0 := by
        nlinarith [himag]
      rcases mul_eq_zero.mp hprod with hab | hsq
      · rcases mul_eq_zero.mp hab with ha0 | hb0
        · exact (ha ha0).elim
        · exact (hb hb0).elim
      · exact sub_eq_zero.mp hsq
    dsimp [gaussianFourthReal] at hreal
    nlinarith [congrArg (fun z : ℚ => z ^ 2) heq, sq_nonneg (a ^ 2)]
  · rintro ⟨t, ht⟩
    refine ⟨t, 0, ?_, ?_⟩
    · simpa [gaussianFourthReal] using ht.symm
    · simp [gaussianFourthImag]

/-- The nonsquare product hypothesis excludes Gaussian fourth powers for
each complementary-pair radicand. -/
theorem complementaryRadicand_not_gaussian_fourth_power
    (d : Fin 4 → ℚ) (S : Finset (Fin 4))
    (hpos : 0 < complementaryRadicand d S)
    (hD : ¬ IsSquare (∏ i, d i))
    (hd : ∀ i, d i ≠ 0) :
    ¬ ∃ a b : ℚ,
      gaussianFourthReal a b = complementaryRadicand d S ∧
      gaussianFourthImag a b = 0 := by
  intro h
  obtain ⟨t, ht⟩ := (positive_gaussian_fourth_power_iff _ hpos).mp h
  exact complementaryRadicand_not_fourth_power d S hD hd ⟨t, ht.symm⟩

/-- The six mixed constituents have this radicand, with `(a,b)` oriented
and `(c,e)` its complementary pair. -/
def mixedRadicand (d : Fin 4 → ℚ) (a b c e : Fin 4) : ℚ :=
  d a ^ 3 * d b * d c ^ 2 * d e ^ 2

/-- The regularity hypothesis directly excludes the negative Gaussian
fourth powers that would make a mixed quartic character principal. -/
theorem mixedRadicand_not_negative_gaussian_fourth_power
    (d : Fin 4 → ℚ) (a b c e : Fin 4)
    (hpos : 0 < mixedRadicand d a b c e)
    (hregular : ¬ ∃ t : ℚ, mixedRadicand d a b c e = 4 * t ^ 4) :
    ¬ ∃ x y : ℚ,
      gaussianFourthReal x y = -mixedRadicand d a b c e ∧
      gaussianFourthImag x y = 0 := by
  exact (negative_gaussian_fourth_power_iff _ hpos).not.mpr hregular

end Erdos940.Quartic
