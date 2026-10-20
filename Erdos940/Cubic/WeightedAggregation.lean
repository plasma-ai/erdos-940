module

public import Erdos940.Cubic.ParameterSelection

/-!
# Weighted aggregation over canonical part triples

The weighted one-part series controls the finite middle family of triples:
triples from `E` for which at least one part lies outside `D`.
-/

@[expose] public section

namespace Erdos940

open scoped Classical

/-- The weight from equation (2) of Beyer–de Ryke. -/
noncomputable def weightedPartWeight (d : CanonicalParts) : ℝ :=
  (3 : ℝ) ^ d.val.primeFactors.card * (d.val : ℝ) ^ (-(1 / 3 : ℝ))

/-- The total weight `H` from equation (2). -/
noncomputable def totalWeightedPartWeight : ℝ :=
  ∑' d : CanonicalParts, weightedPartWeight d

theorem weightedPartWeight_nonneg (d : CanonicalParts) :
    0 ≤ weightedPartWeight d := by
  unfold weightedPartWeight
  positivity

theorem totalWeightedPartWeight_nonneg : 0 ≤ totalWeightedPartWeight := by
  unfold totalWeightedPartWeight
  exact tsum_nonneg weightedPartWeight_nonneg

/-- Finite ordered triples have exactly the cube of the one-part sum. -/
theorem weightedPartTriples_eq_cube (B : Finset CanonicalParts) :
    (∑ d ∈ partTriples B, ∏ i : Fin 3, weightedPartWeight (d i)) =
      (∑ d ∈ B, weightedPartWeight d) ^ 3 := by
  classical
  simpa only [partTriples] using
    (Finset.sum_pow' B weightedPartWeight 3).symm

private theorem partTriples_inter (B D : Finset CanonicalParts) :
    partTriples (B ∩ D) = partTriples B ∩ partTriples D := by
  classical
  ext d
  simp [mem_partTriples, forall_and]

/-- Removing the triples entirely in `D` subtracts their finite cube. -/
theorem weightedMiddle_eq_cubeDiff (D E : Finset CanonicalParts) :
    (∑ d ∈ partTriples E \ partTriples D,
      ∏ i : Fin 3, weightedPartWeight (d i)) =
      (∑ d ∈ E, weightedPartWeight d) ^ 3 -
        (∑ d ∈ E ∩ D, weightedPartWeight d) ^ 3 := by
  classical
  let f : (Fin 3 → CanonicalParts) → ℝ :=
    fun d => ∏ i : Fin 3, weightedPartWeight (d i)
  have hsplit := Finset.sum_inter_add_sum_sdiff
    (partTriples E) (partTriples D) f
  rw [← partTriples_inter] at hsplit
  rw [weightedPartTriples_eq_cube, weightedPartTriples_eq_cube] at hsplit
  dsimp [f] at hsplit
  linarith

private theorem weightedMiddle_le_threeFinite (D E : Finset CanonicalParts) :
    (∑ d ∈ partTriples E \ partTriples D,
      ∏ i : Fin 3, weightedPartWeight (d i)) ≤
      3 * (∑ d ∈ E, weightedPartWeight d) ^ 2 *
        (∑ d ∈ E \ D, weightedPartWeight d) := by
  let U : ℝ := ∑ d ∈ E, weightedPartWeight d
  let V : ℝ := ∑ d ∈ E ∩ D, weightedPartWeight d
  let T : ℝ := ∑ d ∈ E \ D, weightedPartWeight d
  have hUV : U = V + T := by
    simpa only [U, V, T, add_comm] using
      (Finset.sum_inter_add_sum_sdiff E D weightedPartWeight).symm
  have hV : 0 ≤ V := Finset.sum_nonneg fun d _ => weightedPartWeight_nonneg d
  have hT : 0 ≤ T := Finset.sum_nonneg fun d _ => weightedPartWeight_nonneg d
  have hVU : V ≤ U := by linarith
  have hU : 0 ≤ U := by linarith
  have hsq : V ^ 2 ≤ U ^ 2 := by nlinarith
  have hcross : U * V ≤ U ^ 2 := by nlinarith
  have hpoly : U ^ 2 + U * V + V ^ 2 ≤ 3 * U ^ 2 := by nlinarith
  rw [weightedMiddle_eq_cubeDiff]
  change U ^ 3 - V ^ 3 ≤ 3 * U ^ 2 * T
  calc
    U ^ 3 - V ^ 3 = (U - V) * (U ^ 2 + U * V + V ^ 2) := by ring
    _ ≤ (U - V) * (3 * U ^ 2) :=
      mul_le_mul_of_nonneg_left hpoly (sub_nonneg.mpr hVU)
    _ = 3 * U ^ 2 * T := by rw [show U - V = T by linarith]; ring

/-- A finite one-part sum is bounded by the convergent total `H`. -/
theorem weightedPartSum_le_total (B : Finset CanonicalParts) :
    (∑ d ∈ B, weightedPartWeight d) ≤ totalWeightedPartWeight := by
  unfold totalWeightedPartWeight
  exact summable_canonicalPart_weighted.sum_le_tsum B
    (fun d _ => weightedPartWeight_nonneg d)

/-- The weighted part mass in `E \ D` is bounded by the full omitted tail. -/
theorem weightedPartSum_sdiff_le_tail (D E : Finset CanonicalParts) :
    (∑ d ∈ E \ D, weightedPartWeight d) ≤ weightedPartTail D := by
  classical
  let F : Finset {d : CanonicalParts // d ∉ D} :=
    (E \ D).subtype (fun d => d ∉ D)
  have hF : ∀ d ∈ E \ D, d ∉ D := by
    intro d hd
    exact (Finset.mem_sdiff.mp hd).2
  have hsum :
      (∑ d ∈ E \ D, weightedPartWeight d) =
      (∑ d ∈ F, weightedPartWeight d.val) := by
    exact (Finset.sum_subtype_of_mem weightedPartWeight hF).symm
  rw [hsum]
  unfold weightedPartTail
  exact (summable_canonicalPart_weighted.subtype (fun d => d ∉ D)).sum_le_tsum F
    (fun d _ => weightedPartWeight_nonneg d.val)

/-- The middle triple family is controlled by one weighted part tail. -/
theorem weightedMiddle_le_total_tail (D E : Finset CanonicalParts)
    (_hDE : D ⊆ E) :
    (∑ d ∈ partTriples E \ partTriples D,
      ∏ i : Fin 3, weightedPartWeight (d i)) ≤
      3 * totalWeightedPartWeight ^ 2 * weightedPartTail D := by
  let U : ℝ := ∑ d ∈ E, weightedPartWeight d
  let T : ℝ := ∑ d ∈ E \ D, weightedPartWeight d
  have hU : 0 ≤ U := Finset.sum_nonneg fun d _ => weightedPartWeight_nonneg d
  have hT : 0 ≤ T := Finset.sum_nonneg fun d _ => weightedPartWeight_nonneg d
  have hUH : U ≤ totalWeightedPartWeight := weightedPartSum_le_total E
  have hTH : T ≤ weightedPartTail D := weightedPartSum_sdiff_le_tail D E
  have hsq : U ^ 2 ≤ totalWeightedPartWeight ^ 2 := by
    nlinarith [totalWeightedPartWeight_nonneg]
  calc
    (∑ d ∈ partTriples E \ partTriples D,
        ∏ i : Fin 3, weightedPartWeight (d i)) ≤ 3 * U ^ 2 * T :=
      weightedMiddle_le_threeFinite D E
    _ ≤ 3 * totalWeightedPartWeight ^ 2 * T :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) hT
    _ ≤ 3 * totalWeightedPartWeight ^ 2 * weightedPartTail D :=
      mul_le_mul_of_nonneg_left hTH (by positivity)

end Erdos940
