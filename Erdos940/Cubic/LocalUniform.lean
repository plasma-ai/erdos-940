module

public import Erdos940.Cubic.LocalCubic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The eight-term estimate for cubic local counts

This is the character-sum estimate behind Lemma 3.2 of Beyer de Ryke. It is
stated for arbitrary pairs of coefficients and an arbitrary multiplicative
character: once each cubic exponential sum is expressed as two Gauss sums, the
proof only uses the standard Gauss-sum norm and product-of-sums identities.
-/

@[expose] public section

namespace Erdos940

private theorem gaussSum_norm_le_sqrt_card
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ≤ Real.sqrt (Fintype.card F) := by
  by_cases hχ : χ = 1
  · subst χ
    have hψne : ψ ≠ 1 := by simpa using hψ one_ne_zero
    rw [gaussSum_one_left hψne, norm_neg, norm_one]
    have hcard : (1 : ℝ) ≤ Fintype.card F := by
      exact_mod_cast Fintype.card_pos (α := F)
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) :
      (0 : ℝ) ≤ Fintype.card F), Real.sqrt_nonneg (Fintype.card F : ℝ)]
  · have hmul := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq χ ψ] at hmul
    have hnorm := congrArg norm hmul
    have hsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
      simpa only [norm_mul, norm_star, Complex.norm_natCast, pow_two] using hnorm
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) :
      (0 : ℝ) ≤ Fintype.card F), Real.sqrt_nonneg (Fintype.card F : ℝ),
      norm_nonneg (gaussSum χ ψ)]

private theorem mulChar_norm_eq_one_of_ne_zero
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (a : F) (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  obtain ⟨ζ, hζ, hζa⟩ := χ.apply_mem_rootsOfUnity_orderOf ha
  rw [← hζa]
  exact @Complex.norm_eq_one_of_mem_rootsOfUnity ζ (orderOf χ)
    ⟨χ.orderOf_pos.ne'⟩ hζ

/-- The analytic part of the eight-term estimate. Each pair of coefficients
may depend on the coordinate, while the same character occurs in all three
cubic sums. -/
theorem cubicFourierEightTermBound
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (u : F) (hu : u ≠ 0) (A B : Fin 3 → ℂ)
    (hA : ∀ i, ‖A i‖ ≤ Real.sqrt (Fintype.card F))
    (hB : ∀ i, ‖B i‖ ≤ Real.sqrt (Fintype.card F)) :
    ‖∑ s : F, ψ (-s * u) *
        ∏ i : Fin 3, (A i * χ s + B i * χ⁻¹ s)‖ ≤
      8 * (Fintype.card F : ℝ) ^ 2 := by
  classical
  let r : ℝ := Real.sqrt (Fintype.card F)
  let C : (Fin 3 → Bool) → ℂ := fun e =>
    ∏ i : Fin 3, if e i then A i else B i
  let φ : (Fin 3 → Bool) → MulChar F ℂ := fun e =>
    ∏ i : Fin 3, if e i then χ else χ⁻¹
  have hψ' : (ψ.mulShift (-u)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (neg_ne_zero.mpr hu))
  have hexpand (s : F) :
      (∏ i : Fin 3, (A i * χ s + B i * χ⁻¹ s)) =
        ∑ e : Fin 3 → Bool, C e * φ e s := by
    calc
      (∏ i : Fin 3, (A i * χ s + B i * χ⁻¹ s)) =
          ∏ i : Fin 3, ∑ b : Bool,
            if b then A i * χ s else B i * χ⁻¹ s := by
        congr 1
        ext i
        simp
      _ = ∑ e : Fin 3 → Bool,
          ∏ i : Fin 3, if e i then A i * χ s else B i * χ⁻¹ s :=
        Fintype.prod_sum _
      _ = ∑ e : Fin 3 → Bool, C e * φ e s := by
        apply Finset.sum_congr rfl
        intro e _
        have hterm (i : Fin 3) :
            (if e i then A i * χ s else B i * χ⁻¹ s) =
              (if e i then A i else B i) *
                (if e i then χ s else χ⁻¹ s) := by
          split_ifs <;> rfl
        simp_rw [hterm]
        rw [Finset.prod_mul_distrib]
        unfold C φ
        cases h0 : e 0 <;>
          cases h1 : e 1 <;>
          cases h2 : e 2 <;>
          simp only [h0, h1, h2, Bool.false_eq_true,
            ite_true, ite_false, Fin.prod_univ_three, MulChar.mul_apply]
  have hfourier :
      (∑ s : F, ψ (-s * u) *
        ∏ i : Fin 3, (A i * χ s + B i * χ⁻¹ s)) =
      ∑ e : Fin 3 → Bool, C e * gaussSum (φ e) (ψ.mulShift (-u)) := by
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    calc
      (∑ s : F, ψ (-s * u) * (C e * φ e s)) =
          ∑ s : F, C e * (φ e s * ψ (-s * u)) := by
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = C e * ∑ s : F, φ e s * ψ (-s * u) := by
        rw [Finset.mul_sum]
      _ = C e * gaussSum (φ e) (ψ.mulShift (-u)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        simp only [AddChar.mulShift_apply]
        congr 1
        ring
  have hC (e : Fin 3 → Bool) : ‖C e‖ ≤ r ^ 3 := by
    calc
      ‖C e‖ = ∏ i : Fin 3, ‖if e i then A i else B i‖ := by
        simp only [C, norm_prod]
      _ ≤ ∏ _i : Fin 3, r := by
        apply Finset.prod_le_prod₀
        · intro i _
          positivity
        · intro i _
          split_ifs
          · exact hA i
          · exact hB i
      _ = r ^ 3 := by simp
  have hroot : r ^ 2 = (Fintype.card F : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hsingle (e : Fin 3 → Bool) :
      ‖C e * gaussSum (φ e) (ψ.mulShift (-u))‖ ≤
        (Fintype.card F : ℝ) ^ 2 := by
    rw [norm_mul]
    calc
      ‖C e‖ * ‖gaussSum (φ e) (ψ.mulShift (-u))‖ ≤
          r ^ 3 * r := by
        gcongr
        · exact hC e
        · exact gaussSum_norm_le_sqrt_card F (φ e) _ hψ'
      _ = (Fintype.card F : ℝ) ^ 2 := by
        calc
          r ^ 3 * r = (r ^ 2) ^ 2 := by ring
          _ = _ := by rw [hroot]
  rw [hfourier]
  calc
    ‖∑ e : Fin 3 → Bool, C e * gaussSum (φ e) (ψ.mulShift (-u))‖ ≤
        ∑ e : Fin 3 → Bool,
          ‖C e * gaussSum (φ e) (ψ.mulShift (-u))‖ := norm_sum_le _ _
    _ ≤ ∑ _e : Fin 3 → Bool, (Fintype.card F : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro e _
      exact hsingle e
    _ = 8 * (Fintype.card F : ℝ) ^ 2 := by
      simp

/-- Lemma 3.2 follows from the pointwise two-Gauss-sum expression for each
cubic exponential sum. This theorem isolates that identity as an explicit
hypothesis so the local count bound has no hidden analytic assumptions. -/
theorem localCubicCount_bound_of_exponential_sum
    (F : Type*) [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (hExp : ∀ t : F, t ≠ 0 →
      (∑ x : F, ψ (t * x ^ 3)) =
        χ⁻¹ t * gaussSum χ ψ + χ t * gaussSum χ⁻¹ ψ)
    (u : F) (hu : u ≠ 0) (a : Fin 3 → F) (ha : ∀ i, a i ≠ 0) :
    localCubicCount F u a ≤
        Fintype.card F * Fintype.card F + 8 * Fintype.card F ∧
      Fintype.card F * Fintype.card F ≤
        localCubicCount F u a + 8 * Fintype.card F := by
  classical
  let A : Fin 3 → ℂ := fun i => gaussSum χ⁻¹ ψ * χ (a i)
  let B : Fin 3 → ℂ := fun i => gaussSum χ ψ * χ⁻¹ (a i)
  have hA (i : Fin 3) : ‖A i‖ ≤ Real.sqrt (Fintype.card F) := by
    dsimp [A]
    rw [norm_mul, mulChar_norm_eq_one_of_ne_zero F χ (a i) (ha i), mul_one]
    exact gaussSum_norm_le_sqrt_card F χ⁻¹ ψ hψ
  have hB (i : Fin 3) : ‖B i‖ ≤ Real.sqrt (Fintype.card F) := by
    dsimp [B]
    rw [norm_mul, mulChar_norm_eq_one_of_ne_zero F χ⁻¹ (a i) (ha i), mul_one]
    exact gaussSum_norm_le_sqrt_card F χ ψ hψ
  have hterm (s : F) (hs : s ≠ 0) (i : Fin 3) :
      (∑ x : F, ψ (s * a i * x ^ 3)) =
        A i * χ s + B i * χ⁻¹ s := by
    have ht : s * a i ≠ 0 := mul_ne_zero hs (ha i)
    rw [hExp (s * a i) ht]
    simp only [map_mul]
    dsimp [A, B]
    ring
  let f : F → ℂ := fun s => ψ (-s * u) *
    ∏ i : Fin 3, ∑ x : F, ψ (s * a i * x ^ 3)
  let g : F → ℂ := fun s => ψ (-s * u) *
    ∏ i : Fin 3, (A i * χ s + B i * χ⁻¹ s)
  have hfzero : f 0 = (Fintype.card F : ℂ) ^ 3 := by
    simp [f, Fin.prod_univ_three, pow_three, mul_assoc]
  have hgzero : g 0 = 0 := by
    simp [g, Fin.prod_univ_three, MulChar.map_zero]
  have hfg (s : F) (hs : s ≠ 0) : f s = g s := by
    simp only [f, g]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact hterm s hs i
  have hfourier :
      (Fintype.card F : ℂ) * (localCubicCount F u a : ℂ) =
        (Fintype.card F : ℂ) ^ 3 + ∑ s : F, g s := by
    calc
      (Fintype.card F : ℂ) * (localCubicCount F u a : ℂ) =
          ∑ s : F, f s := localCubicCount_fourier F ψ hψ u a
      _ = f 0 + ∑ s ∈ (Finset.univ : Finset F).erase 0, f s := by
        calc
          _ = (∑ s ∈ (Finset.univ : Finset F).erase 0, f s) + f 0 :=
            (Finset.sum_erase_add _ _ (Finset.mem_univ 0)).symm
          _ = _ := add_comm _ _
      _ = (Fintype.card F : ℂ) ^ 3 +
          ∑ s ∈ (Finset.univ : Finset F).erase 0, g s := by
        rw [hfzero]
        congr 1
        apply Finset.sum_congr rfl
        intro s hs
        exact hfg s (Finset.ne_of_mem_erase hs)
      _ = (Fintype.card F : ℂ) ^ 3 + ∑ s : F, g s := by
        congr 1
        calc
          _ = (∑ s ∈ (Finset.univ : Finset F).erase 0, g s) + g 0 := by
            rw [hgzero, add_zero]
          _ = _ := Finset.sum_erase_add _ _ (Finset.mem_univ 0)
  have hE : ‖∑ s : F, g s‖ ≤ 8 * (Fintype.card F : ℝ) ^ 2 :=
    cubicFourierEightTermBound F χ ψ hψ u hu A B hA hB
  have hmain :
      (Fintype.card F : ℂ) *
          ((localCubicCount F u a : ℂ) - (Fintype.card F : ℂ) ^ 2) =
        ∑ s : F, g s := by
    calc
      _ = (Fintype.card F : ℂ) * (localCubicCount F u a : ℂ) -
          (Fintype.card F : ℂ) ^ 3 := by ring
      _ = ∑ s : F, g s := by rw [hfourier]; ring
  have hqpos : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hdev :
      ‖(localCubicCount F u a : ℂ) - (Fintype.card F : ℂ) ^ 2‖ ≤
        8 * (Fintype.card F : ℝ) := by
    have hn := congrArg norm hmain
    rw [norm_mul, Complex.norm_natCast] at hn
    rw [← hn] at hE
    nlinarith
  have hreal :
      |(localCubicCount F u a : ℝ) - (Fintype.card F : ℝ) ^ 2| ≤
        8 * (Fintype.card F : ℝ) := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hdev
  constructor
  · have := (abs_le.mp hreal).2
    exact_mod_cast (show (localCubicCount F u a : ℝ) ≤
      (Fintype.card F : ℝ) * Fintype.card F + 8 * Fintype.card F by nlinarith)
  · have := (abs_le.mp hreal).1
    exact_mod_cast (show (Fintype.card F : ℝ) * Fintype.card F ≤
      (localCubicCount F u a : ℝ) + 8 * Fintype.card F by nlinarith)

/-- The prime-field form of Lemma 3.2, using the cubic exponential-sum
identity in `LocalCubic`. -/
theorem localCubicCount_nonzero_coefficients_bound_via_gauss
    (q : ℕ) [Fact q.Prime] (hq : q % 3 = 1)
    (u : ZMod q) (hu : u ≠ 0) (a : Fin 3 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    localCubicCount (ZMod q) u a ≤ q * q + 8 * q ∧
      q * q ≤ localCubicCount (ZMod q) u a + 8 * q := by
  obtain ⟨χ, hχ⟩ := exists_cubic_character q hq
  let ψ : AddChar (ZMod q) ℂ :=
    AddChar.FiniteField.primitiveChar_to_Complex (ZMod q)
  have hψ : ψ.IsPrimitive :=
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod q)
  have hExp (t : ZMod q) (ht : t ≠ 0) :=
    cubic_exponential_sum_eq_gauss q χ hχ ψ hψ t ht
  simpa [ZMod.card q] using
    localCubicCount_bound_of_exponential_sum (ZMod q) χ ψ hψ hExp u hu a ha

end Erdos940
