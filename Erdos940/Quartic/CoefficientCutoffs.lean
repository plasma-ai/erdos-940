import Erdos940.Quartic.CoefficientMajorant
import Erdos940.Quartic.ParameterChoice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Coefficient cutoffs for the quartic argument

The coefficient-prime tail has a power saving, so it survives the fixed
21st power of the sieve logarithm. After that cutoff has been chosen, a
finite family of canonical coefficients captures all but an arbitrarily
small amount of the remaining summable coefficient weight.
-/

namespace Erdos940.Quartic

open Filter
open scoped Topology

/-- Every fixed power of `log (2B)` is absorbed by `B⁻ᐩη`. -/
theorem tendsto_log_two_mul_pow_mul_rpow_neg (η : ℝ) (hη : 0 < η) (k : ℝ) :
    Tendsto (fun B : ℕ => Real.log (2 * (B : ℝ)) ^ k * (B : ℝ) ^ (-η))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x ^ k / x ^ η) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop k hη).tendsto_div_nhds_zero
  have htwo : Tendsto (fun B : ℕ => 2 * (B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hscaled : Tendsto
      (fun B : ℕ => (2 : ℝ) ^ η *
        (Real.log (2 * (B : ℝ)) ^ k / (2 * (B : ℝ)) ^ η)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hlog.comp htwo) :
      Tendsto (fun B : ℕ => (2 : ℝ) ^ η *
        (Real.log (2 * (B : ℝ)) ^ k / (2 * (B : ℝ)) ^ η))
        atTop (𝓝 ((2 : ℝ) ^ η * 0)))
  apply hscaled.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
  have hBr : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  rw [Real.mul_rpow (by norm_num) hBr.le, Real.rpow_neg hBr.le]
  have htwo_ne : (2 : ℝ) ^ η ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hB_ne : (B : ℝ) ^ η ≠ 0 := (Real.rpow_pos_of_pos hBr _).ne'
  field_simp

/-- Equation (23), with every constant fixed before the prime cutoff is
chosen. The bound holds for every larger cutoff as well. -/
theorem exists_primeCutoff_tail_log_bound
    (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 20)
    (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, 0 < B ∧
      K * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0) < δ := by
  classical
  let C : ℝ := ∑' d : Fin 4 → CanonicalParts,
    (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
      (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact tsum_nonneg fun _ => by positivity
  have hlim : Tendsto
      (fun B : ℕ => K * C *
        (Real.log (2 * (B : ℝ)) ^ (30 : ℝ) * (B : ℝ) ^ (-η)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_log_two_mul_pow_mul_rpow_neg η hη0 30) :
      Tendsto (fun B : ℕ => (K * C) *
        (Real.log (2 * (B : ℝ)) ^ (30 : ℝ) * (B : ℝ) ^ (-η)))
        atTop (𝓝 ((K * C) * 0)))
  have hsmall : ∀ᶠ B : ℕ in atTop,
      K * C * (Real.log (2 * (B : ℝ)) ^ (30 : ℝ) * (B : ℝ) ^ (-η)) < δ :=
    hlim.eventually (eventually_lt_nhds hδ)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp
    (Filter.Eventually.and (eventually_ge_atTop (1 : ℕ)) hsmall)
  refine ⟨B₀, fun B hB => ?_⟩
  obtain ⟨hB1, hsmallB⟩ := hB₀ B hB
  have hBpos : 0 < B := by omega
  refine ⟨hBpos, ?_⟩
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
    linarith
  have htail := coefficientOmegaWeight_primeTail_bound η hη0.le hη B hBpos
  calc
    K * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0)
        ≤ K * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
            ((B : ℝ) ^ (-η) * C) := by
              exact mul_le_mul_of_nonneg_left htail
                (mul_nonneg hK (pow_nonneg hlog _))
    _ = K * C *
          (Real.log (2 * (B : ℝ)) ^ (30 : ℝ) * (B : ℝ) ^ (-η)) := by
            have hpow : Real.log (2 * (B : ℝ)) ^ (30 : ℝ) =
                Real.log (2 * (B : ℝ)) ^ (30 : ℕ) := by
              norm_num [Real.rpow_natCast]
            rw [hpow]
            ring
    _ < δ := hsmallB

/-- A finite set of individual coefficients captures all but an arbitrarily
small part of any nonnegative summable weight on coefficient quadruples.
The set may be required to contain an already chosen finite family. -/
theorem exists_finite_coefficient_family_tail_lt
    (w : (Fin 4 → CanonicalParts) → ℝ) (hw : Summable w)
    (hw0 : ∀ d, 0 ≤ w d) (E₀ : Finset CanonicalParts)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ E : Finset CanonicalParts, E₀ ⊆ E ∧
      (∑' d : Fin 4 → CanonicalParts,
        if ∀ i, d i ∈ E then 0 else w d) < δ := by
  classical
  obtain ⟨S, hS⟩ := (summable_iff_vanishing_norm.mp hw)
    (δ / 2) (by linarith)
  let E : Finset CanonicalParts :=
    E₀ ∪ S.biUnion (fun d => Finset.univ.image d)
  have hSE (d : Fin 4 → CanonicalParts) (hd : d ∈ S) (i : Fin 4) :
      d i ∈ E := by
    simp only [E, Finset.mem_union, Finset.mem_biUnion]
    right
    refine ⟨d, hd, ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have htail_bound :
      (∑' d : Fin 4 → CanonicalParts,
        if ∀ i, d i ∈ E then 0 else w d) ≤ δ / 2 := by
    apply Real.tsum_le_of_sum_le (fun d => by
      split_ifs with h
      · exact le_refl _
      · exact hw0 d)
    intro t
    let t' := t.filter (fun d => ¬∀ i, d i ∈ E)
    have ht'S : Disjoint t' S := by
      apply Finset.disjoint_left.mpr
      intro d hdt' hdS
      have hdout : ¬∀ i, d i ∈ E := (Finset.mem_filter.mp hdt').2
      exact hdout (fun i => hSE d hdS i)
    apply le_of_lt
    calc
      (∑ d ∈ t, if ∀ i, d i ∈ E then 0 else w d)
          = ∑ d ∈ t', w d := by
              simp only [t', Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro d hd
              by_cases h : ∀ i, d i ∈ E <;> simp [h]
      _ ≤ ‖∑ d ∈ t', w d‖ := le_abs_self _
      _ < δ / 2 := hS t' ht'S
  refine ⟨E, Finset.subset_union_left, ?_⟩
  linarith

/-- Equation (24) for the quartic coefficient majorant, after all earlier
parameters have been fixed. -/
theorem exists_coefficientOmegaWeight_finite_family_tail_lt
    (E₀ : Finset CanonicalParts) (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ E : Finset CanonicalParts, E₀ ⊆ E ∧
      K * (∑' d : Fin 4 → CanonicalParts,
        if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) < δ := by
  obtain ⟨E, hE, htail⟩ :=
    exists_finite_coefficient_family_tail_lt coefficientOmegaWeight
      summable_coefficientOmegaWeight
      (fun d => by unfold coefficientOmegaWeight; positivity)
      E₀ (δ / (K + 1)) (by positivity)
  refine ⟨E, hE, ?_⟩
  have htail_nonneg : 0 ≤
      (∑' d : Fin 4 → CanonicalParts,
        if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) := by
    exact tsum_nonneg fun d => by
      split_ifs
      · exact le_refl _
      · unfold coefficientOmegaWeight
        positivity
  have hK1 : 0 < K + 1 := by linarith
  have hdiv : (K + 1) * (δ / (K + 1)) = δ := by
    field_simp
  have hmul := mul_lt_mul_of_pos_left htail hK1
  rw [hdiv] at hmul
  nlinarith

/-- The analytic cutoffs can be taken in the order `T`, `B`, then `E`.
The first damping weight and rate may be any pointwise positive summable
family; the two remaining tails use the quartic coefficient majorant. -/
theorem exists_ordered_coefficient_cutoffs
    (w c : (Fin 4 → CanonicalParts) → ℝ)
    (hw : Summable w) (hw0 : ∀ d, 0 ≤ w d) (hc : ∀ d, 0 < c d)
    (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 20)
    (K : ℕ → ℝ) (hK : ∀ T, 0 ≤ K T)
    (E₀ : Finset CanonicalParts) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T B : ℕ, ∃ E : Finset CanonicalParts,
      (∑' d, w d * Real.exp (-((T : ℝ) * c d))) < δ ∧
      0 < B ∧
      K T * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0) < δ ∧
      E₀ ⊆ E ∧
      K T * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) < δ := by
  classical
  obtain ⟨T₀, hT₀⟩ :=
    exists_nat_forall_ge_tsum_weight_mul_exp_neg_lt w c hw hw0 hc hδ
  let T := T₀
  have hT := hT₀ T (le_refl T)
  obtain ⟨B₀, hB₀⟩ := exists_primeCutoff_tail_log_bound η hη0 hη
    (K T) δ (hK T) hδ
  let B := max B₀ 1
  obtain ⟨hBpos, hBtail⟩ := hB₀ B (le_max_left _ _)
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) := by
    apply Real.log_nonneg
    have hBr : (1 : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast (le_max_right B₀ 1)
    linarith
  obtain ⟨E, hE, hEtail⟩ :=
    exists_coefficientOmegaWeight_finite_family_tail_lt E₀
      (K T * Real.log (2 * (B : ℝ)) ^ (30 : ℕ)) δ
      (mul_nonneg (hK T) (pow_nonneg hlog _)) hδ
  exact ⟨T, B, E, hT, hBpos, hBtail, hE, hEtail⟩

end Erdos940.Quartic
