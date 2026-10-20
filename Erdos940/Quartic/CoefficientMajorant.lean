import Erdos940.Quartic.FixedParts

/-!
# A summable coefficient majorant

The factors `4 ^ ω(dᵢ)` dominate `4 ^ ω(∏ dᵢ)`, and the four individual
weighted canonical-part series converge for every exponent above `1/5`.
This supplies the summability required by the quartic sieve without an
Euler-product expansion for the coefficient tuples.
-/

namespace Erdos940.Quartic

noncomputable def coefficientProduct (d : Fin 4 → CanonicalParts) : ℕ :=
  ∏ i, (d i).val

noncomputable def coefficientOmegaWeight (d : Fin 4 → CanonicalParts) : ℝ :=
  (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
    (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ))

private noncomputable def separatedOmegaWeight (s : ℝ)
    (d : Fin 4 → CanonicalParts) : ℝ :=
  ∏ i, (4 : ℝ) ^ (d i).val.primeFactors.card * ((d i).val : ℝ) ^ (-s)

private theorem summable_separatedOmegaWeight (s : ℝ) (hs : 1 / 5 < s) :
    Summable (separatedOmegaWeight s) := by
  let w : CanonicalParts → ℝ := fun a =>
    (4 : ℝ) ^ a.val.primeFactors.card * (a.val : ℝ) ^ (-s)
  have hw : Summable w := summable_canonicalPart_weighted s hs
  have hw0 : ∀ a, 0 ≤ w a := fun _ => by dsimp [w]; positivity
  let e : (Fin 4 → CanonicalParts) ≃
      CanonicalParts × (CanonicalParts × (CanonicalParts × CanonicalParts)) :=
    { toFun := fun d => (d 0, (d 1, (d 2, d 3)))
      invFun := fun t i =>
        if i = 0 then t.1
        else if i = 1 then t.2.1
        else if i = 2 then t.2.2.1
        else t.2.2.2
      left_inv := by
        intro d
        funext i
        fin_cases i <;> simp
      right_inv := by
        rintro ⟨a, b, c, d⟩
        simp }
  have h34 : Summable (fun t : CanonicalParts × CanonicalParts =>
      w t.1 * w t.2) := hw.mul_of_nonneg hw hw0 hw0
  have h234 : Summable (fun t : CanonicalParts ×
      (CanonicalParts × CanonicalParts) =>
      w t.1 * (w t.2.1 * w t.2.2)) :=
    hw.mul_of_nonneg h34 hw0 (fun t => mul_nonneg (hw0 t.1) (hw0 t.2))
  have h1234 : Summable (fun t : CanonicalParts ×
      (CanonicalParts × (CanonicalParts × CanonicalParts)) =>
      w t.1 * (w t.2.1 * (w t.2.2.1 * w t.2.2.2))) :=
    hw.mul_of_nonneg h234 hw0 (fun t =>
      mul_nonneg (hw0 t.1) (mul_nonneg (hw0 t.2.1) (hw0 t.2.2)))
  have h := h1234.comp_injective e.injective
  exact h.congr (fun d => by
    change w (d 0) * (w (d 1) * (w (d 2) * w (d 3))) =
      separatedOmegaWeight s d
    simp only [separatedOmegaWeight, Fin.prod_univ_four, w]
    ring)

private theorem primeFactors_card_mul_le (a b : ℕ) :
    (a * b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  rw [Nat.primeFactors_mul ha hb]
  exact Finset.card_union_le _ _

private theorem primeFactors_card_product_le (d : Fin 4 → CanonicalParts) :
    (coefficientProduct d).primeFactors.card ≤
      ∑ i : Fin 4, (d i).val.primeFactors.card := by
  simp only [coefficientProduct, Fin.prod_univ_four, Fin.sum_univ_four]
  have h1 := primeFactors_card_mul_le ((d 0).val * (d 1).val) (d 2).val
  have h2 := primeFactors_card_mul_le ((d 0).val * (d 1).val * (d 2).val) (d 3).val
  have h3 := primeFactors_card_mul_le (d 0).val (d 1).val
  omega

private theorem coefficientOmegaWeight_le_separated (s : ℝ)
    (d : Fin 4 → CanonicalParts) :
    (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
      (coefficientProduct d : ℝ) ^ (-s) ≤ separatedOmegaWeight s d := by
  have hcard := primeFactors_card_product_le d
  have hpow : (4 : ℝ) ^ (coefficientProduct d).primeFactors.card ≤
      (4 : ℝ) ^ (∑ i : Fin 4, (d i).val.primeFactors.card) := by
    exact pow_le_pow_right₀ (by norm_num) hcard
  have hprod : (coefficientProduct d : ℝ) ^ (-s) =
      ∏ i : Fin 4, ((d i).val : ℝ) ^ (-s) := by
    unfold coefficientProduct
    rw [Nat.cast_prod]
    exact (Real.finsetProd_rpow _ _ (by
      intro i hi
      have hdi : 0 < (d i).val := CanonicalPart.pos (d i).property
      exact_mod_cast hdi.le) _).symm
  rw [hprod]
  calc
    _ ≤ (4 : ℝ) ^ (∑ i : Fin 4, (d i).val.primeFactors.card) *
          ∏ i : Fin 4, ((d i).val : ℝ) ^ (-s) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = separatedOmegaWeight s d := by
      have hsplit :
          (4 : ℝ) ^ (∑ i : Fin 4, (d i).val.primeFactors.card) =
            ∏ i : Fin 4, (4 : ℝ) ^ (d i).val.primeFactors.card := by
        simp only [Fin.sum_univ_four, Fin.prod_univ_four, pow_add]
      rw [hsplit]
      unfold separatedOmegaWeight
      rw [Finset.prod_mul_distrib]

/-- The coefficient series with a factor `4 ^ ω(D)` converges whenever the
power of `D` is strictly beyond the canonical-part threshold `1/5`. -/
theorem summable_coefficientOmegaWeightExp (s : ℝ) (hs : 1 / 5 < s) :
    Summable (fun d : Fin 4 → CanonicalParts =>
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        (coefficientProduct d : ℝ) ^ (-s)) := by
  apply Summable.of_nonneg_of_le
    (fun d => by positivity)
    (fun d => coefficientOmegaWeight_le_separated s d)
  exact summable_separatedOmegaWeight s hs

/-- Equation (2) of the quartic argument: an arbitrary fixed positive
power below `1/20` may be absorbed into the coefficient sum. -/
theorem summable_coefficientOmegaWeight_eta (η : ℝ) (hη : η < 1 / 20) :
    Summable (fun d : Fin 4 → CanonicalParts =>
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η)) := by
  have hs : 1 / 5 < (1 / 4 : ℝ) - η := by linarith
  have he : -((1 / 4 : ℝ) - η) = -(1 / 4 : ℝ) + η := by ring
  simpa only [he] using
    summable_coefficientOmegaWeightExp ((1 / 4 : ℝ) - η) hs

theorem summable_coefficientOmegaWeight : Summable coefficientOmegaWeight := by
  change Summable (fun d : Fin 4 → CanonicalParts =>
    (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
      (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ)))
  exact summable_coefficientOmegaWeightExp (1 / 4 : ℝ) (by norm_num)

private theorem coefficientProduct_pos (d : Fin 4 → CanonicalParts) :
    0 < coefficientProduct d := by
  unfold coefficientProduct
  exact Finset.prod_pos (fun i _ => CanonicalPart.pos (d i).property)

/-- Pointwise large-coefficient tail estimate. It is enough to obtain
power decay for tuples containing a prime above the cutoff, since such a
tuple has product at least the cutoff. -/
theorem coefficientOmegaWeight_large_bound (η : ℝ) (hη : 0 ≤ η)
    (B : ℕ) (hB : 0 < B) (d : Fin 4 → CanonicalParts)
    (hBD : B ≤ coefficientProduct d) :
    coefficientOmegaWeight d ≤ (B : ℝ) ^ (-η) *
      ((4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η)) := by
  let D := coefficientProduct d
  have hD : 0 < (D : ℝ) := by exact_mod_cast coefficientProduct_pos d
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hBDr : (B : ℝ) ≤ (D : ℝ) := by exact_mod_cast hBD
  have htail : (D : ℝ) ^ (-η) ≤ (B : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_nonpos hBr hBDr (neg_nonpos.mpr hη)
  have hfactor : (D : ℝ) ^ (-(1 / 4 : ℝ)) =
      (D : ℝ) ^ (-(1 / 4 : ℝ) + η) * (D : ℝ) ^ (-η) := by
    rw [← Real.rpow_add hD]
    congr 1
    ring
  unfold coefficientOmegaWeight
  change (4 : ℝ) ^ D.primeFactors.card * (D : ℝ) ^ (-(1 / 4 : ℝ)) ≤ _
  rw [hfactor]
  calc
    _ ≤ (4 : ℝ) ^ D.primeFactors.card *
        ((D : ℝ) ^ (-(1 / 4 : ℝ) + η) * (B : ℝ) ^ (-η)) := by
      gcongr
    _ = _ := by ring

/-- Power saving on the total coefficient weight once the product of the
four coefficients exceeds `B`. This is a stronger tail than mere
summability and absorbs every fixed power of `log B`. -/
theorem coefficientOmegaWeight_productTail_bound (η : ℝ)
    (hη0 : 0 ≤ η) (hη : η < 1 / 20) (B : ℕ) (hB : 0 < B) :
    (∑' d : Fin 4 → CanonicalParts,
        if B ≤ coefficientProduct d then coefficientOmegaWeight d else 0) ≤
      (B : ℝ) ^ (-η) *
        ∑' d : Fin 4 → CanonicalParts,
          (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
            (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η) := by
  let f : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    if B ≤ coefficientProduct d then coefficientOmegaWeight d else 0
  let g : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
      (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η)
  have hg : Summable g := summable_coefficientOmegaWeight_eta η hη
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
      (fun d => by
        simp only [f]
        split_ifs
        · unfold coefficientOmegaWeight
          positivity
        · positivity)
      (fun d => by
        simp only [f]
        split_ifs
        · exact le_refl _
        · unfold coefficientOmegaWeight
          positivity)
    exact summable_coefficientOmegaWeight
  have hfg (d : Fin 4 → CanonicalParts) :
      f d ≤ (B : ℝ) ^ (-η) * g d := by
    by_cases hd : B ≤ coefficientProduct d
    · simpa [f, g, hd] using
        coefficientOmegaWeight_large_bound η hη0 B hB d hd
    · simp only [f, hd, ↓reduceIte]
      exact mul_nonneg (by positivity) (by dsimp [g]; positivity)
  have hsum := hf.tsum_le_tsum hfg (hg.mul_left ((B : ℝ) ^ (-η)))
  simpa only [f, g, hg.tsum_mul_left] using hsum

/-- The same power saving for tuples with a coefficient prime exceeding
`B`, the tail appearing in the quartic sieve. -/
theorem coefficientOmegaWeight_primeTail_bound (η : ℝ)
    (hη0 : 0 ≤ η) (hη : η < 1 / 20) (B : ℕ) (hB : 0 < B) :
    (∑' d : Fin 4 → CanonicalParts,
      if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
        coefficientOmegaWeight d else 0) ≤
      (B : ℝ) ^ (-η) *
        ∑' d : Fin 4 → CanonicalParts,
          (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
            (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η) := by
  classical
  let f : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
      coefficientOmegaWeight d else 0
  let g : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    if B ≤ coefficientProduct d then coefficientOmegaWeight d else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
      (fun d => by
        simp only [f]
        split_ifs
        · unfold coefficientOmegaWeight
          positivity
        · positivity)
      (fun d => by
        simp only [f]
        split_ifs
        · exact le_refl _
        · unfold coefficientOmegaWeight
          positivity)
    exact summable_coefficientOmegaWeight
  have hg : Summable g := by
    apply Summable.of_nonneg_of_le
      (fun d => by
        simp only [g]
        split_ifs
        · unfold coefficientOmegaWeight
          positivity
        · positivity)
      (fun d => by
        simp only [g]
        split_ifs
        · exact le_refl _
        · unfold coefficientOmegaWeight
          positivity)
    exact summable_coefficientOmegaWeight
  have hfg (d : Fin 4 → CanonicalParts) : f d ≤ g d := by
    by_cases hp : ∃ p ∈ (coefficientProduct d).primeFactors, B < p
    · have hp' := hp
      obtain ⟨p, hmem, hBp⟩ := hp
      have hBD : B ≤ coefficientProduct d := by
        have hpD : p ≤ coefficientProduct d :=
          Nat.le_of_dvd (coefficientProduct_pos d) (Nat.dvd_of_mem_primeFactors hmem)
        omega
      simp only [f, g, hp', hBD, ↓reduceIte, le_refl]
    · simp only [f, hp, ↓reduceIte]
      unfold g
      split_ifs
      · unfold coefficientOmegaWeight
        positivity
      · exact le_refl _
  have hsum := hf.tsum_le_tsum hfg hg
  exact hsum.trans (coefficientOmegaWeight_productTail_bound η hη0 hη B hB)

end Erdos940.Quartic
