import Erdos940.Quartic.GaussianDiskEstimate
import Erdos940.Quartic.GaussianLBoundAnalytic

/-!
# Norm-indexed coefficients of a periodic Gaussian angular sum

This module groups the lattice points by squared norm. The finite disk
bound becomes a bound on the partial sums of the resulting Dirichlet-series
coefficients; the count of lattice points gives the absolute-coefficient
majorant required by partial summation.
-/

namespace Erdos940.Quartic.GaussianCoefficientLBound

open Finset
open Erdos940.Quartic.GaussianLBound
open Erdos940.Quartic.GaussianDiskEstimate
open Erdos940.Quartic.GaussianCellPartition
open Erdos940.Quartic.GaussianLBoundAnalytic

def gaussianNormSq (p : ℤ × ℤ) : ℕ := p.1.natAbs ^ 2 + p.2.natAbs ^ 2

theorem gaussianNormSq_cast (p : ℤ × ℤ) :
    (gaussianNormSq p : ℤ) = p.1 ^ 2 + p.2 ^ 2 := by
  simp [gaussianNormSq]

theorem mem_integerNormBall_iff_normSq (X : ℕ) (p : ℤ × ℤ) :
    p ∈ integerNormBall X ↔ gaussianNormSq p ≤ X := by
  rw [mem_integerNormBall_iff, ← gaussianNormSq_cast]
  exact_mod_cast (Iff.rfl : gaussianNormSq p ≤ X ↔ gaussianNormSq p ≤ X)

def gaussianNormShell (n : ℕ) : Finset (ℤ × ℤ) :=
  (integerNormBall n).filter (fun p => gaussianNormSq p = n)

theorem mem_gaussianNormShell_iff (n : ℕ) (p : ℤ × ℤ) :
    p ∈ gaussianNormShell n ↔ gaussianNormSq p = n := by
  simp only [gaussianNormShell, Finset.mem_filter, mem_integerNormBall_iff_normSq]
  exact ⟨And.right, fun h => ⟨h.le, h⟩⟩

theorem gaussianNormSq_eq_zero_iff (p : ℤ × ℤ) :
    gaussianNormSq p = 0 ↔ p = (0, 0) := by
  constructor
  · intro h
    have h' : p.1 = 0 ∧ p.2 = 0 := by simpa [gaussianNormSq] using h
    exact Prod.ext h'.1 h'.2
  · rintro rfl
    simp [gaussianNormSq]

noncomputable def gaussianAngularCoeff (q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ gaussianNormShell n,
    ω (cellOffset q hq p) * angularTwo (integerPairComplex p)

private def nonzeroBall (n : ℕ) : Finset (ℤ × ℤ) :=
  (integerNormBall n).erase (0, 0)

private theorem mem_nonzeroBall_iff (n : ℕ) (p : ℤ × ℤ) :
    p ∈ nonzeroBall n ↔ p ≠ (0, 0) ∧ gaussianNormSq p ≤ n := by
  simp [nonzeroBall, mem_integerNormBall_iff_normSq]

private theorem shell_eq_ball_fiber (n k : ℕ) (hk : k ∈ Finset.Icc 1 n) :
    gaussianNormShell k =
      (nonzeroBall n).filter (fun p => gaussianNormSq p = k) := by
  ext p
  rw [mem_gaussianNormShell_iff, Finset.mem_filter, mem_nonzeroBall_iff]
  obtain ⟨hklo, hkhi⟩ := Finset.mem_Icc.mp hk
  constructor
  · intro hp
    refine ⟨⟨?_, ?_⟩, hp⟩
    · intro hz
      subst p
      simp [gaussianNormSq] at hp
      omega
    · omega
  · exact And.right

/-- Finite coefficient partial sums are exactly the weighted Gaussian disk
sum, since the zero lattice point has vanishing type-two angular factor. -/
theorem sum_gaussianAngularCoeff_eq_disk (X q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, gaussianAngularCoeff q hq ω n) =
      ∑ p ∈ integerNormBall X,
        ω (cellOffset q hq p) * angularTwo (integerPairComplex p) := by
  classical
  let w : (ℤ × ℤ) → ℂ := fun p =>
    ω (cellOffset q hq p) * angularTwo (integerPairComplex p)
  have hmaps : ∀ p ∈ nonzeroBall X, gaussianNormSq p ∈ Finset.Icc 1 X := by
    intro p hp
    obtain ⟨hne, hle⟩ := (mem_nonzeroBall_iff X p).mp hp
    apply Finset.mem_Icc.mpr
    constructor
    · have hpos : gaussianNormSq p ≠ 0 := by
        intro hz
        exact hne ((gaussianNormSq_eq_zero_iff p).mp hz)
      omega
    · exact hle
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := nonzeroBall X) (t := Finset.Icc 1 X)
    (g := gaussianNormSq) (f := w) hmaps
  have hzero : w (0, 0) = 0 := by
    simp [w, integerPairComplex, angularTwo]
  calc
    (∑ n ∈ Finset.Icc 1 X, gaussianAngularCoeff q hq ω n) =
        ∑ n ∈ Finset.Icc 1 X,
          ∑ p ∈ (nonzeroBall X).filter (fun p => gaussianNormSq p = n), w p := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [gaussianAngularCoeff, w]
      rw [shell_eq_ball_fiber X n hn]
    _ = ∑ p ∈ nonzeroBall X, w p := hfiber
    _ = ∑ p ∈ integerNormBall X, w p := by
      exact Finset.sum_erase _ hzero

theorem sum_shells_eq_ball {A : Type*} [AddCommMonoid A]
    (X : ℕ) (w : (ℤ × ℤ) → A) (hzero : w (0, 0) = 0) :
    (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ gaussianNormShell n, w p) =
      ∑ p ∈ integerNormBall X, w p := by
  classical
  have hmaps : ∀ p ∈ nonzeroBall X, gaussianNormSq p ∈ Finset.Icc 1 X := by
    intro p hp
    obtain ⟨hne, hle⟩ := (mem_nonzeroBall_iff X p).mp hp
    apply Finset.mem_Icc.mpr
    constructor
    · have hpos : gaussianNormSq p ≠ 0 := by
        intro hz
        exact hne ((gaussianNormSq_eq_zero_iff p).mp hz)
      omega
    · exact hle
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := nonzeroBall X) (t := Finset.Icc 1 X)
    (g := gaussianNormSq) (f := w) hmaps
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ gaussianNormShell n, w p) =
        ∑ n ∈ Finset.Icc 1 X,
          ∑ p ∈ (nonzeroBall X).filter (fun p => gaussianNormSq p = n), w p := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [shell_eq_ball_fiber X n hn]
    _ = ∑ p ∈ nonzeroBall X, w p := hfiber
    _ = ∑ p ∈ integerNormBall X, w p := Finset.sum_erase _ hzero

/-- Uniform linear absolute-coefficient bound, from the surrounding
integer square. -/
theorem sum_norm_gaussianAngularCoeff_le (X q : ℕ) (hq : 0 < q)
    (ω : Fin q × Fin q → ℂ) (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    (∑ n ∈ Finset.Icc 1 X, ‖gaussianAngularCoeff q hq ω n‖) ≤ 9 * X := by
  let w : (ℤ × ℤ) → ℝ := fun p =>
    ‖ω (cellOffset q hq p) * angularTwo (integerPairComplex p)‖
  have hzero : w (0, 0) = 0 := by
    simp [w, integerPairComplex, angularTwo]
  have hsum : (∑ n ∈ Finset.Icc 1 X, ∑ p ∈ gaussianNormShell n, w p) =
      ∑ p ∈ integerNormBall X, w p := sum_shells_eq_ball X w hzero
  have hcoeff : (∑ n ∈ Finset.Icc 1 X, ‖gaussianAngularCoeff q hq ω n‖) ≤
      ∑ n ∈ Finset.Icc 1 X, ∑ p ∈ gaussianNormShell n, w p := by
    apply Finset.sum_le_sum
    intro n hn
    exact norm_sum_le _ _
  have hterm (p : ℤ × ℤ) : w p ≤ 1 := by
    dsimp [w]
    rw [norm_mul]
    calc
      ‖ω (cellOffset q hq p)‖ * ‖angularTwo (integerPairComplex p)‖ ≤ 1 * 1 :=
        mul_le_mul (hunit _) (norm_angularTwo_le_one _) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
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

/-- The concrete periodic type-two coefficient sums satisfy the desired
square-root cancellation bound. -/
theorem norm_sum_gaussianAngularCoeff_le (X q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 X, gaussianAngularCoeff q (NeZero.pos q) ω n‖ ≤
      81 * ((q : ℝ) * (Nat.sqrt X : ℝ) + (q : ℝ) ^ 2) := by
  rw [sum_gaussianAngularCoeff_eq_disk]
  exact norm_weighted_integerNormBall_le X q ω hmean hunit

/-- Uniform logarithmic L-series bound for the concrete norm-indexed
periodic type-two Gaussian coefficients. The rational period `q` gives
cutoff `q²`; a Gaussian ideal character of norm `Q` can take `q=Q`. -/
theorem norm_gaussianAngularLSeries_le_log (q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ uv : Fin q × Fin q, ω uv) = 0)
    (hunit : ∀ uv, ‖ω uv‖ ≤ 1)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianAngularCoeff q (NeZero.pos q) ω) (σ : ℂ)‖ ≤
      162 * Real.log ((q : ℝ) ^ 2) + 648 := by
  let f := gaussianAngularCoeff q (NeZero.pos q) ω
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqnonneg : (0 : ℝ) ≤ q := le_of_lt hqpos
  have hQ : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    nlinarith
  have hAbs : ∀ n, (∑ k ∈ Finset.Icc 1 n, ‖f k‖) ≤ 81 * n := by
    intro n
    have h := sum_norm_gaussianAngularCoeff_le n q (NeZero.pos q) ω hunit
    dsimp [f]
    nlinarith
  have hCancel : ∀ t, (q : ℝ) ^ 2 < t →
      ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤
        81 * (((q : ℝ) ^ 2) ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + (q : ℝ) ^ 2) := by
    intro t ht
    have htpos : 0 ≤ t := le_trans (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2) ht.le
    have hbound := norm_sum_gaussianAngularCoeff_le ⌊t⌋₊ q ω hmean hunit
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
    nlinarith
  have h := norm_LSeries_le_log_of_partial_sum_bounds f 81 ((q : ℝ) ^ 2) σ
    (by norm_num) hQ hσ₁ hσ₂ hAbs hCancel
  calc
    ‖LSeries (gaussianAngularCoeff q (NeZero.pos q) ω) (σ : ℂ)‖ ≤
        2 * 81 * Real.log ((q : ℝ) ^ 2) + 8 * 81 := h
    _ = 162 * Real.log ((q : ℝ) ^ 2) + 648 := by ring

end Erdos940.Quartic.GaussianCoefficientLBound
