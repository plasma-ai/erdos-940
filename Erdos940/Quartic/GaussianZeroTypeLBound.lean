import Erdos940.Quartic.GaussianCoefficientLBound

/-!
# Periodic Gaussian coefficients of infinity type zero

A zero-mean periodic weight cancels exactly in each complete square cell.
Only cells crossing the disk boundary remain. The same rational-period
cutoff as for infinity type two then gives a logarithmic L-series bound.
-/

namespace Erdos940.Quartic.GaussianZeroTypeLBound

open Finset Classical
open Erdos940.Quartic.GaussianLBound
open Erdos940.Quartic.GaussianCellPartition
open Erdos940.Quartic.GaussianCoefficientLBound
open Erdos940.Quartic.GaussianLBoundAnalytic

theorem cellOffset_origin (q : ℕ) [NeZero q] :
    cellOffset q (NeZero.pos q) (0, 0) = ((0 : Fin q), (0 : Fin q)) := by
  simpa [GaussianCellPartition.signedCellPoint] using
    cellOffset_signedCellPoint q (NeZero.pos q) 0 0 (0 : Fin q) (0 : Fin q)

private theorem norm_cell_weight_sum_le (q : ℕ) (ω : Fin q × Fin q → ℂ)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) (T : Finset (Fin q × Fin q)) :
    ‖∑ uv ∈ T, ω uv‖ ≤ (q : ℝ) ^ 2 := by
  calc
    ‖∑ uv ∈ T, ω uv‖ ≤ ∑ uv ∈ T, ‖ω uv‖ := norm_sum_le _ _
    _ ≤ ∑ _uv ∈ T, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro uv _
      exact hunit uv
    _ = T.card := by simp
    _ ≤ (q : ℝ) ^ 2 := by
      have hcard : T.card ≤ q ^ 2 := by
        calc
          T.card ≤ Fintype.card (Fin q × Fin q) := Finset.card_le_univ _
          _ = q ^ 2 := by simp [Fintype.card_prod, pow_two]
      exact_mod_cast hcard

private theorem norm_cell_zero_le (q : ℕ) (S : Finset (ℤ × ℤ))
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) (c : ℤ × ℤ) :
    ‖∑ uv ∈ cellOffsets q S c, ω uv‖ ≤
      if PartialCell q S c then (q : ℝ) ^ 2 else 0 := by
  by_cases hfull : cellOffsets q S c = Finset.univ
  · have hnotpartial : ¬ PartialCell q S c := by
      intro h
      exact h.2 hfull
    simp [hfull, hmean, hnotpartial]
  · by_cases hempty : cellOffsets q S c = ∅
    · have hnotpartial : ¬ PartialCell q S c := by
        simp [PartialCell, hempty]
      simp [hempty, hnotpartial]
    · have hpartial : PartialCell q S c :=
        ⟨Finset.nonempty_iff_ne_empty.mpr hempty, hfull⟩
      simpa [hpartial] using
        norm_cell_weight_sum_le q ω hunit (cellOffsets q S c)

private theorem norm_periodic_sum_le_partial_cells (q R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ latticeBox R)
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    ‖∑ p ∈ S, ω (cellOffset q hq p)‖ ≤
      (q : ℝ) ^ 2 * (partialCells q R S).card := by
  have hpartition := sum_by_cellIndexBox q R hq S hS
    (fun p => ω (cellOffset q hq p))
  simp_rw [cellOffset_signedCellPoint q hq] at hpartition
  rw [← hpartition]
  calc
    ‖∑ c ∈ cellIndexBox q R, ∑ uv ∈ cellOffsets q S c, ω uv‖ ≤
        ∑ c ∈ cellIndexBox q R, ‖∑ uv ∈ cellOffsets q S c, ω uv‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c ∈ cellIndexBox q R,
          if PartialCell q S c then (q : ℝ) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro c hc
      exact norm_cell_zero_le q S ω hmean hunit c
    _ = (q : ℝ) ^ 2 * (partialCells q R S).card := by
      simp [partialCells, Finset.sum_ite, mul_comm]

/-- Type-zero periodic lattice cancellation in an integer disk. -/
theorem norm_periodic_integerNormBall_le (X q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    ‖∑ p ∈ integerNormBall X, ω (cellOffset q (NeZero.pos q) p)‖ ≤
      8 * ((q : ℝ) * (Nat.sqrt X : ℝ) + 2 * (q : ℝ) ^ 2) := by
  let R := Nat.sqrt X
  have hsubset : integerNormBall X ⊆ latticeBox R := by
    intro p hp
    change p ∈ integerBox R
    exact mem_integerBox_of_normSq_le X p ((mem_integerNormBall_iff X p).mp hp)
  have hbase := norm_periodic_sum_le_partial_cells q R (NeZero.pos q)
    (integerNormBall X) hsubset ω hmean hunit
  have hpartial := disk_partialCells_card_le X q R (NeZero.pos q)
    (integerNormBall X) (mem_integerNormBall_iff X)
  have hqpos : (0 : ℝ) ≤ q := by exact_mod_cast Nat.zero_le q
  have hdiv : ((R / q : ℕ) : ℝ) * (q : ℝ) ≤ R := by
    exact_mod_cast Nat.div_mul_le_self R q
  have hmul := mul_le_mul_of_nonneg_left hdiv hqpos
  have hpartial' : ((partialCells q R (integerNormBall X)).card : ℝ) ≤
      8 * ((R / q + 2 : ℕ) : ℝ) := by exact_mod_cast hpartial
  have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := sq_nonneg _
  have hweighted := mul_le_mul_of_nonneg_left hpartial' hq2
  dsimp [R] at *
  push_cast at *
  nlinarith

noncomputable def zeroTypeWeight (q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) (p : ℤ × ℤ) : ℂ :=
  if p = (0, 0) then 0 else ω (cellOffset q hq p)

noncomputable def gaussianZeroCoeff (q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ gaussianNormShell n, zeroTypeWeight q hq ω p

theorem sum_gaussianZeroCoeff_eq_disk (X q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, gaussianZeroCoeff q hq ω n) =
      ∑ p ∈ integerNormBall X, zeroTypeWeight q hq ω p := by
  have hzero : zeroTypeWeight q hq ω (0, 0) = 0 := by
    simp [zeroTypeWeight]
  exact sum_shells_eq_ball X (zeroTypeWeight q hq ω) hzero

theorem sum_norm_gaussianZeroCoeff_le (X q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 X, ‖gaussianZeroCoeff q hq ω n‖) ≤ 9 * X := by
  let w : (ℤ × ℤ) → ℝ := fun p => ‖zeroTypeWeight q hq ω p‖
  have hzero : w (0, 0) = 0 := by simp [w, zeroTypeWeight]
  have hsum : (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ gaussianNormShell n, w p) =
      ∑ p ∈ integerNormBall X, w p := sum_shells_eq_ball X w hzero
  have hcoeff : (∑ n ∈ Finset.Icc 1 X, ‖gaussianZeroCoeff q hq ω n‖) ≤
      ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ gaussianNormShell n, w p := by
    apply Finset.sum_le_sum
    intro n hn
    exact norm_sum_le _ _
  have hterm (p : ℤ × ℤ) : w p ≤ 1 := by
    by_cases hp : p = (0, 0)
    · simp [w, zeroTypeWeight, hp]
    · simpa [w, zeroTypeWeight, hp] using hunit (cellOffset q hq p)
  have hcount : (∑ p ∈ integerNormBall X, w p) ≤
      (integerNormBall X).card := by
    calc
      (∑ p ∈ integerNormBall X, w p) ≤
          ∑ _p ∈ integerNormBall X, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hterm p
      _ = (integerNormBall X).card := by simp
  by_cases hX : X = 0
  · subst X
    simp
  · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
    have hcard := integerNormBall_card_le_nine_mul X hXpos
    have hcard' : ((integerNormBall X).card : ℝ) ≤ 9 * X := by
      exact_mod_cast hcard
    exact hcoeff.trans (hsum.le.trans (hcount.trans hcard'))

/-- The extra condition at the zero residue is automatic for a finite
Dirichlet character extended by zero on nonunits. -/
theorem norm_sum_gaussianZeroCoeff_le (X q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1)
    (hzero : ω (cellOffset q (NeZero.pos q) (0, 0)) = 0) :
    ‖∑ n ∈ Finset.Icc 1 X, gaussianZeroCoeff q (NeZero.pos q) ω n‖ ≤
      8 * ((q : ℝ) * (Nat.sqrt X : ℝ) + 2 * (q : ℝ) ^ 2) := by
  rw [sum_gaussianZeroCoeff_eq_disk]
  have hw : ∀ p, zeroTypeWeight q (NeZero.pos q) ω p =
      ω (cellOffset q (NeZero.pos q) p) := by
    intro p
    by_cases hp : p = (0, 0)
    · subst p
      simp [zeroTypeWeight, hzero]
    · simp [zeroTypeWeight, hp]
  simp_rw [hw]
  exact norm_periodic_integerNormBall_le X q ω hmean hunit

/-- Uniform logarithmic bound for the concrete type-zero Gaussian
L-series, with cutoff at the square of the rational period. -/
theorem norm_gaussianZeroLSeries_le_log (q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1)
    (hzero : ω (cellOffset q (NeZero.pos q) (0, 0)) = 0)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianZeroCoeff q (NeZero.pos q) ω) (σ : ℂ)‖ ≤
      162 * Real.log ((q : ℝ) ^ 2) + 648 := by
  let f := gaussianZeroCoeff q (NeZero.pos q) ω
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqnonneg : (0 : ℝ) ≤ q := le_of_lt hqpos
  have hQ : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    nlinarith
  have hAbs : ∀ n, (∑ k ∈ Finset.Icc 1 n, ‖f k‖) ≤ 81 * n := by
    intro n
    have h := sum_norm_gaussianZeroCoeff_le n q (NeZero.pos q) ω hunit
    dsimp [f]
    nlinarith
  have hCancel : ∀ t, (q : ℝ) ^ 2 < t →
      ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤
        81 * (((q : ℝ) ^ 2) ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + (q : ℝ) ^ 2) := by
    intro t ht
    have htpos : 0 ≤ t := le_trans (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2) ht.le
    have hbound := norm_sum_gaussianZeroCoeff_le ⌊t⌋₊ q ω hmean hunit hzero
    have hnat : ((Nat.sqrt ⌊t⌋₊ : ℕ) : ℝ) ^ 2 ≤ t := by
      have hs := Nat.sqrt_le' ⌊t⌋₊
      have hs' : ((Nat.sqrt ⌊t⌋₊ : ℕ) : ℝ) ^ 2 ≤ (⌊t⌋₊ : ℝ) := by
        exact_mod_cast hs
      exact hs'.trans (Nat.floor_le htpos)
    have hroot : ((Nat.sqrt ⌊t⌋₊ : ℕ) : ℝ) ≤ Real.sqrt t := by
      have hsqrt := Real.sq_sqrt htpos
      have hnonneg : (0 : ℝ) ≤ (Nat.sqrt ⌊t⌋₊ : ℕ) := by positivity
      nlinarith [Real.sqrt_nonneg t]
    have hmul := mul_le_mul_of_nonneg_left hroot hqnonneg
    have hqroot : ((q : ℝ) ^ 2) ^ (1 / 2 : ℝ) = (q : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hqnonneg]
    have htroot : t ^ (1 / 2 : ℝ) = Real.sqrt t :=
      (Real.sqrt_eq_rpow t).symm
    rw [hqroot, htroot]
    dsimp [f] at hbound ⊢
    nlinarith [sq_nonneg (q : ℝ)]
  have h := norm_LSeries_le_log_of_partial_sum_bounds f 81 ((q : ℝ) ^ 2) σ
    (by norm_num) hQ hσ₁ hσ₂ hAbs hCancel
  calc
    ‖LSeries (gaussianZeroCoeff q (NeZero.pos q) ω) (σ : ℂ)‖ ≤
        2 * 81 * Real.log ((q : ℝ) ^ 2) + 8 * 81 := h
    _ = 162 * Real.log ((q : ℝ) ^ 2) + 648 := by ring

end Erdos940.Quartic.GaussianZeroTypeLBound
