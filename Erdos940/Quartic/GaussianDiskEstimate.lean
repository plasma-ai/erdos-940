import Erdos940.Quartic.GaussianCellPartition
import Erdos940.Quartic.GaussianSignedShell

/-!
# A common discrete main term for Gaussian residue classes

On each complete square cell every residue sees one point, and the
angular factor differs from the cell-corner value by `O(1/radius)`.
Partial cells and the central cell contribute at most one per residue.
The main term below is a finite common sum, avoiding any integration
convention; its cancellation against a zero-mean character is exact.
-/

namespace Erdos940.Quartic.GaussianDiskEstimate

open Finset
open Erdos940.Quartic.GaussianLBound
open Erdos940.Quartic.GaussianCellPartition
open Erdos940.Quartic.GaussianSignedShell
open Classical

private noncomputable def pointAngular (q : ℕ) (c : ℤ × ℤ) (uv : Fin q × Fin q) : ℂ :=
  angularTwo (GaussianLBound.signedCellPoint q c.1 c.2 uv.1 uv.2)

private noncomputable def cellClassTerm (q : ℕ) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) (uv : Fin q × Fin q) : ℂ :=
  if GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S
  then pointAngular q c uv else 0

private noncomputable def cellMainTerm (q : ℕ) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) : ℂ :=
  if cellOffsets q S c = Finset.univ ∧ c ≠ (0, 0)
  then angularTwo (GaussianLBound.signedCellPoint q c.1 c.2 0 0) else 0

private theorem pointAngular_le_one (q : ℕ) (c : ℤ × ℤ)
    (uv : Fin q × Fin q) : ‖pointAngular q c uv‖ ≤ 1 :=
  norm_angularTwo_le_one _

private theorem reciprocalMax_nonneg (c : ℤ × ℤ) :
    0 ≤ reciprocalMax c := by
  unfold reciprocalMax
  split_ifs <;> positivity

private theorem cell_class_error_le (q : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (uv : Fin q × Fin q) :
    ‖cellClassTerm q S c uv - cellMainTerm q S c‖ ≤
      8 * reciprocalMax c +
        (if PartialCell q S c then (1 : ℝ) else 0) +
        (if c = (0, 0) then (1 : ℝ) else 0) := by
  classical
  by_cases hfull : cellOffsets q S c = Finset.univ
  · by_cases hc : c = (0, 0)
    · subst c
      have hmem : GaussianCellPartition.signedCellPoint q 0 0 uv.1 uv.2 ∈ S := by
        have hu : uv ∈ cellOffsets q S (0, 0) := by rw [hfull]; simp
        simpa [cellOffsets] using hu
      have hnotpartial : ¬ PartialCell q S (0, 0) := by
        intro h
        exact h.2 hfull
      simpa [cellClassTerm, cellMainTerm, hmem, hnotpartial,
        pointAngular, reciprocalMax] using pointAngular_le_one q (0, 0) uv
    · have hmem : GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S := by
        have hu : uv ∈ cellOffsets q S c := by rw [hfull]; simp
        simpa [cellOffsets] using hu
      have hnotpartial : ¬ PartialCell q S c := by
        intro h
        exact h.2 hfull
      have hk : 0 < max c.1.natAbs c.2.natAbs := by
        by_contra hn
        have h₁ : c.1 = 0 := by omega
        have h₂ : c.2 = 0 := by omega
        exact hc (Prod.ext h₁ h₂)
      have hvar := norm_angularTwo_signedCell_sub_base_le q c.1 c.2
        uv.1 uv.2 hq hk uv.1.isLt uv.2.isLt
      have hrecip : reciprocalMax c =
          (max c.1.natAbs c.2.natAbs : ℝ)⁻¹ := by
        simp [reciprocalMax, ne_of_gt hk]
      simpa [cellClassTerm, cellMainTerm, hmem, hfull, hc,
        pointAngular, hnotpartial, hrecip, div_eq_mul_inv,
        norm_sub_rev] using hvar
  · by_cases hnone : cellOffsets q S c = ∅
    · have hmem : GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2 ∉ S := by
        intro hm
        have hu : uv ∈ cellOffsets q S c := by simpa [cellOffsets] using hm
        rw [hnone] at hu
        simp at hu
      have hnotpartial : ¬ PartialCell q S c := by
        simp [PartialCell, hnone]
      have hmain : cellMainTerm q S c = 0 := by
        simp [cellMainTerm, hfull]
      have hterm : cellClassTerm q S c uv = 0 := by
        simp [cellClassTerm, hmem]
      rw [hmain, hterm]
      simp only [sub_self, norm_zero, hnotpartial, ite_false]
      have hr := reciprocalMax_nonneg c
      split_ifs <;> linarith
    · have hpartial : PartialCell q S c := by
        exact ⟨Finset.nonempty_iff_ne_empty.mpr hnone, hfull⟩
      have hmain : cellMainTerm q S c = 0 := by
        simp [cellMainTerm, hfull]
      have hr := reciprocalMax_nonneg c
      by_cases hmem : GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S
      · have hbound := pointAngular_le_one q c uv
        rw [hmain]
        simp only [cellClassTerm, hmem, ite_true, sub_zero, hpartial, ite_true]
        split_ifs <;> linarith
      · have hterm : cellClassTerm q S c uv = 0 := by
          simp [cellClassTerm, hmem]
        rw [hmain, hterm]
        simp only [sub_self, norm_zero, hpartial, ite_true]
        split_ifs <;> linarith

/-- Angular sum in one residue class, over a finite lattice region. -/
noncomputable def classAngularSum (q R : ℕ) (S : Finset (ℤ × ℤ))
    (uv : Fin q × Fin q) : ℂ :=
  ∑ c ∈ cellIndexBox q R, cellClassTerm q S c uv

/-- The complete-cell corner sum, shared by every residue class. -/
noncomputable def commonAngularMain (q R : ℕ) (S : Finset (ℤ × ℤ)) : ℂ :=
  ∑ c ∈ cellIndexBox q R, cellMainTerm q S c

/-- A discrete version of the per-residue Riemann-sum estimate: all
residue classes share a common main term, and their deviations are
controlled by the signed radial shell sum and the number of partial cells. -/
theorem norm_classAngularSum_sub_commonMain_le (q R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (uv : Fin q × Fin q) :
    ‖classAngularSum q R S uv - commonAngularMain q R S‖ ≤
      64 * ((R / q + 1 : ℕ) : ℝ) + (partialCells q R S).card + 1 := by
  classical
  let B := cellIndexBox q R
  let N := R / q + 1
  have hB : B = integerBox N := rfl
  have hcenter : (0, 0) ∈ B := by
    rw [hB, mem_integerBox_iff_natAbs_le]
    simp
  have hradial : (∑ c ∈ B, reciprocalMax c) ≤ 8 * N := by
    simpa only [hB, reciprocalBoxSum] using reciprocalBoxSum_le_eight_mul N
  have hpartial : (∑ c ∈ B,
        if PartialCell q S c then (1 : ℝ) else 0) =
        (partialCells q R S).card := by
    calc
      (∑ c ∈ B, if PartialCell q S c then (1 : ℝ) else 0) =
          ∑ c ∈ B.filter (PartialCell q S), (1 : ℝ) := by
        simp
      _ = (partialCells q R S).card := by
        simp [partialCells, B]
  have hcentral : (∑ c ∈ B,
        if c = (0, 0) then (1 : ℝ) else 0) = 1 := by
    simp [hcenter]
  have hpointwise (c : ℤ × ℤ) (hc : c ∈ B) :
      ‖cellClassTerm q S c uv - cellMainTerm q S c‖ ≤
        8 * reciprocalMax c +
          (if PartialCell q S c then (1 : ℝ) else 0) +
          (if c = (0, 0) then (1 : ℝ) else 0) :=
    cell_class_error_le q hq S c uv
  have hdiff : classAngularSum q R S uv - commonAngularMain q R S =
      ∑ c ∈ B, (cellClassTerm q S c uv - cellMainTerm q S c) := by
    simp [classAngularSum, commonAngularMain, B, Finset.sum_sub_distrib]
  rw [hdiff]
  calc
    ‖∑ c ∈ B, (cellClassTerm q S c uv - cellMainTerm q S c)‖ ≤
        ∑ c ∈ B, ‖cellClassTerm q S c uv - cellMainTerm q S c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c ∈ B, (8 * reciprocalMax c +
          (if PartialCell q S c then (1 : ℝ) else 0) +
          (if c = (0, 0) then (1 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      exact hpointwise
    _ = 8 * (∑ c ∈ B, reciprocalMax c) +
          (partialCells q R S).card + 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hpartial, hcentral]
    _ ≤ 64 * ((R / q + 1 : ℕ) : ℝ) + (partialCells q R S).card + 1 := by
      have hm := mul_le_mul_of_nonneg_left hradial (by norm_num : (0 : ℝ) ≤ 8)
      dsimp [N] at hm
      nlinarith

/-- Every residue class in the integer disk has the same finite main term,
up to an error linear in the number of cell layers. This is the discrete
counterpart of equation (6), with no integral normalization needed. -/
theorem norm_disk_classAngularSum_sub_commonMain_le (X q : ℕ)
    (hq : 0 < q) (uv : Fin q × Fin q) :
    ‖classAngularSum q (Nat.sqrt X) (integerNormBall X) uv -
      commonAngularMain q (Nat.sqrt X) (integerNormBall X)‖ ≤
      81 * ((Nat.sqrt X / q + 1 : ℕ) : ℝ) := by
  let R := Nat.sqrt X
  let N := R / q + 1
  have hbase := norm_classAngularSum_sub_commonMain_le q R hq
    (integerNormBall X) uv
  have hpartial := GaussianCellPartition.disk_partialCells_card_le
    X q R hq (integerNormBall X) (mem_integerNormBall_iff X)
  have hN : 1 ≤ N := by
    change 1 ≤ R / q + 1
    exact Nat.le_add_left 1 (R / q)
  have hpartial' : ((partialCells q R (integerNormBall X)).card : ℝ) ≤
      8 * ((R / q + 2 : ℕ) : ℝ) := by exact_mod_cast hpartial
  dsimp [R, N] at *
  push_cast at *
  nlinarith

/-- The common main term cancels against any zero-mean periodic weight. -/
theorem norm_weighted_disk_classes_le (X q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    ‖∑ uv : Fin q × Fin q,
      ω uv * classAngularSum q (Nat.sqrt X) (integerNormBall X) uv‖ ≤
      (q : ℝ) ^ 2 * (81 * ((Nat.sqrt X / q + 1 : ℕ) : ℝ)) := by
  have h := norm_weighted_sum_le_card_mul_error ω
    (classAngularSum q (Nat.sqrt X) (integerNormBall X))
    (commonAngularMain q (Nat.sqrt X) (integerNormBall X))
    (81 * ((Nat.sqrt X / q + 1 : ℕ) : ℝ)) hmean hunit
    (norm_disk_classAngularSum_sub_commonMain_le X q (NeZero.pos q))
  simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using h

private theorem signedPointComplex (q : ℕ) (c : ℤ × ℤ)
    (uv : Fin q × Fin q) :
    integerPairComplex
      (GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2) =
      GaussianLBound.signedCellPoint q c.1 c.2 uv.1 uv.2 := by
  rfl

/-- The cell-index definition is the literal sum over lattice points in
one residue class. -/
theorem classAngularSum_eq_lattice_class_sum (q R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ latticeBox R)
    (uv : Fin q × Fin q) :
    classAngularSum q R S uv =
      ∑ p ∈ S,
        if cellOffset q hq p = uv then angularTwo (integerPairComplex p) else 0 := by
  classical
  let f : (ℤ × ℤ) → ℂ := fun p =>
    if cellOffset q hq p = uv then angularTwo (integerPairComplex p) else 0
  have hpartition := sum_by_cellIndexBox q R hq S hS f
  rw [← hpartition]
  unfold classAngularSum
  apply Finset.sum_congr rfl
  intro c hc
  simp only [f]
  simp_rw [cellOffset_signedCellPoint q hq]
  rw [Finset.sum_ite_eq']
  by_cases hm : uv ∈ cellOffsets q S c
  · have hpoint : GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S := by
      simpa [cellOffsets] using hm
    simp [cellClassTerm, hpoint, pointAngular, signedPointComplex, hm]
  · have hpoint : GaussianCellPartition.signedCellPoint q c.1 c.2 uv.1 uv.2 ∉ S := by
      intro hp
      exact hm (by simpa [cellOffsets] using hp)
    simp [cellClassTerm, hpoint, hm]

/-- Reindexing the complete residue sum recovers the genuine periodic
weighted Gaussian lattice sum. -/
theorem weighted_classes_eq_lattice (q R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ latticeBox R)
    (ω : Fin q × Fin q → ℂ) :
    (∑ uv : Fin q × Fin q, ω uv * classAngularSum q R S uv) =
      ∑ p ∈ S,
        ω (cellOffset q hq p) * angularTwo (integerPairComplex p) := by
  classical
  simp_rw [classAngularSum_eq_lattice_class_sum q R hq S hS]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp [mul_ite]

/-- Concrete cancellation for a periodic mean-zero Gaussian weight of
infinity type two. Here `q²` is the rational Gaussian modulus norm.
This is the finite partial-sum estimate behind equation (7). -/
theorem norm_weighted_integerNormBall_le (X q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    ‖∑ p ∈ integerNormBall X,
      ω (cellOffset q (NeZero.pos q) p) * angularTwo (integerPairComplex p)‖ ≤
      81 * ((q : ℝ) * (Nat.sqrt X : ℝ) + (q : ℝ) ^ 2) := by
  let R := Nat.sqrt X
  have hsubset : integerNormBall X ⊆ latticeBox R := by
    intro p hp
    change p ∈ integerBox R
    exact mem_integerBox_of_normSq_le X p ((mem_integerNormBall_iff X p).mp hp)
  have hreindex := weighted_classes_eq_lattice q R (NeZero.pos q)
    (integerNormBall X) hsubset ω
  have hbound := norm_weighted_disk_classes_le X q ω hmean hunit
  rw [hreindex] at hbound
  have hqpos : (0 : ℝ) ≤ q := by exact_mod_cast Nat.zero_le q
  have hdiv : ((R / q : ℕ) : ℝ) * (q : ℝ) ≤ R := by
    exact_mod_cast Nat.div_mul_le_self R q
  have hmul := mul_le_mul_of_nonneg_left hdiv hqpos
  dsimp [R] at *
  push_cast at *
  nlinarith

end Erdos940.Quartic.GaussianDiskEstimate
