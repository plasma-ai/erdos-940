import Erdos940.Quartic.GaussianHeckeLBridge
import Erdos940.Quartic.GaussianConductorPeriodicity

/-!
# Vanishing of the finite mean of a quartic Gaussian character

The quartic ideal symbol is extended by zero at ideals sharing a prime factor
with `2R`. Multiplication by an admissible Gaussian integer acts on this
extension by a scalar. If that integer induces a permutation of the residue
classes of a period and the scalar is nontrivial, the finite mean is zero.
-/

namespace Erdos940.Quartic.GaussianZeroMean

open scoped NumberField
open Erdos940.Quartic
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianCellPartition

/-- A nonidentity fourth root remains nonidentity under a complex embedding. -/
theorem gaussianQuarticComplexValue_ne_one
    (ι : GaussianField →+* ℂ)
    (ζ : rootsOfUnity 4 (𝓞 GaussianField)) (hζ : ζ ≠ 1) :
    gaussianQuarticComplexValue ι ζ ≠ 1 := by
  intro h
  have hfield : (((ζ : (𝓞 GaussianField)ˣ) : 𝓞 GaussianField) : GaussianField) = 1 :=
    ι.injective (by simpa [gaussianQuarticComplexValue] using h)
  have hr : (((ζ : (𝓞 GaussianField)ˣ) : 𝓞 GaussianField)) = 1 := by
    exact_mod_cast hfield
  have hu : (ζ : (𝓞 GaussianField)ˣ) = 1 := Units.ext hr
  exact hζ (by exact_mod_cast hu)

/-- A good product ideal has good factors. -/
theorem goodIdeal_of_mul_left
    (R : 𝓞 GaussianField) (I J : Ideal (𝓞 GaussianField))
    (h : GaussianQuarticGoodIdeal R (I * J)) :
    GaussianQuarticGoodIdeal R I := by
  refine ⟨(mul_ne_zero_iff.mp h.1).1, ?_⟩
  intro P hP
  exact h.2 P (hP.trans (dvd_mul_right I J))

/-- A good product ideal has good factors. -/
theorem goodIdeal_of_mul_right
    (R : 𝓞 GaussianField) (I J : Ideal (𝓞 GaussianField))
    (h : GaussianQuarticGoodIdeal R (I * J)) :
    GaussianQuarticGoodIdeal R J := by
  refine ⟨(mul_ne_zero_iff.mp h.1).2, ?_⟩
  intro P hP
  exact h.2 P (hP.trans (dvd_mul_left J I))

/-- The good-ideal condition is multiplicative in both directions. -/
theorem goodIdeal_mul_iff
    (R : 𝓞 GaussianField) (I J : Ideal (𝓞 GaussianField)) :
    GaussianQuarticGoodIdeal R (I * J) ↔
      GaussianQuarticGoodIdeal R I ∧ GaussianQuarticGoodIdeal R J := by
  exact ⟨fun h => ⟨goodIdeal_of_mul_left R I J h,
    goodIdeal_of_mul_right R I J h⟩,
    fun h => gaussianQuarticGoodIdeal_mul R I J h.1 h.2⟩

/-- The complex-valued extension of the quartic ideal symbol by zero. -/
noncomputable def quarticIdealWeight
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I : Ideal (𝓞 GaussianField)) : ℂ := by
  classical
  exact if h : GaussianQuarticGoodIdeal R I then
    gaussianQuarticComplexValue ι (gaussianQuarticIdealSymbol R I h)
  else 0

/-- The zero-extended quartic ideal symbol is multiplicative. -/
theorem quarticIdealWeight_mul
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I J : Ideal (𝓞 GaussianField)) :
    quarticIdealWeight R ι (I * J) =
      quarticIdealWeight R ι I * quarticIdealWeight R ι J := by
  classical
  by_cases hI : GaussianQuarticGoodIdeal R I
  · by_cases hJ : GaussianQuarticGoodIdeal R J
    · have hIJ := gaussianQuarticGoodIdeal_mul R I J hI hJ
      simp only [quarticIdealWeight, dif_pos hI, dif_pos hJ, dif_pos hIJ]
      rw [gaussianQuarticIdealSymbol_mul R I J hI hJ]
      exact map_mul ι _ _
    · have hIJ : ¬ GaussianQuarticGoodIdeal R (I * J) :=
        fun h => hJ (goodIdeal_of_mul_right R I J h)
      simp [quarticIdealWeight, hJ, hIJ]
  · have hIJ : ¬ GaussianQuarticGoodIdeal R (I * J) :=
      fun h => hI (goodIdeal_of_mul_left R I J h)
    simp [quarticIdealWeight, hI, hIJ]

/-- The product of two coordinate pairs, using Gaussian multiplication. -/
def gaussianPairMul (a b : ℤ × ℤ) : ℤ × ℤ :=
  let z : GaussianInt := ⟨a.1, a.2⟩ * ⟨b.1, b.2⟩
  (z.re, z.im)

theorem gaussianPointInteger_pairMul (a b : ℤ × ℤ) :
    gaussianPointInteger (gaussianPairMul a b) =
      gaussianPointInteger a * gaussianPointInteger b := by
  change gaussianFourthIntegerRingEquiv
      (⟨((⟨a.1, a.2⟩ : GaussianInt) * ⟨b.1, b.2⟩).re,
        ((⟨a.1, a.2⟩ : GaussianInt) * ⟨b.1, b.2⟩).im⟩) = _
  rw [show (⟨((⟨a.1, a.2⟩ : GaussianInt) * ⟨b.1, b.2⟩).re,
        ((⟨a.1, a.2⟩ : GaussianInt) * ⟨b.1, b.2⟩).im⟩ : GaussianInt) =
      (⟨a.1, a.2⟩ : GaussianInt) * ⟨b.1, b.2⟩ from by ext <;> rfl]
  exact map_mul gaussianFourthIntegerRingEquiv _ _

/-- The lattice weight is the ideal weight on the principal ideal. -/
theorem quarticIdealLatticeWeight_eq_idealWeight
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (p : ℤ × ℤ) :
    quarticIdealLatticeWeight R ι p =
      quarticIdealWeight R ι (Ideal.span {gaussianPointInteger p}) := by
  rfl

/-- The quartic lattice character, extended by zero, is multiplicative. -/
theorem quarticIdealLatticeWeight_pairMul
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (a b : ℤ × ℤ) :
    quarticIdealLatticeWeight R ι (gaussianPairMul a b) =
      quarticIdealLatticeWeight R ι a * quarticIdealLatticeWeight R ι b := by
  rw [quarticIdealLatticeWeight_eq_idealWeight,
    quarticIdealLatticeWeight_eq_idealWeight,
    quarticIdealLatticeWeight_eq_idealWeight,
    gaussianPointInteger_pairMul, ← Ideal.span_singleton_mul_span_singleton]
  exact quarticIdealWeight_mul R ι _ _

/-- Multiplication by a Gaussian integer on two coordinates modulo `q`. -/
def gaussianResidueMul (q : ℕ) (a : ℤ × ℤ)
    (xy : ZMod q × ZMod q) : ZMod q × ZMod q :=
  ((a.1 : ZMod q) * xy.1 - (a.2 : ZMod q) * xy.2,
    (a.2 : ZMod q) * xy.1 + (a.1 : ZMod q) * xy.2)

/-- The residue action is ordinary Gaussian multiplication in coordinates. -/
theorem gaussianResidueMul_intCast (q : ℕ) (a b : ℤ × ℤ) :
    gaussianResidueMul q a ((b.1 : ZMod q), (b.2 : ZMod q)) =
      (((gaussianPairMul a b).1 : ZMod q),
        ((gaussianPairMul a b).2 : ZMod q)) := by
  apply Prod.ext <;>
    simp [gaussianResidueMul, gaussianPairMul] <;> ring

/-- Multiplication by a Gaussian integer permutes the residue plane when
its norm is invertible modulo the period. -/
def gaussianResidueMulEquiv (q : ℕ) (a : ℤ × ℤ)
    (t : ZMod q)
    (ht : t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2) = 1) :
    (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun := gaussianResidueMul q a
  invFun := fun xy =>
    (t * ((a.1 : ZMod q) * xy.1 + (a.2 : ZMod q) * xy.2),
      t * (-(a.2 : ZMod q) * xy.1 + (a.1 : ZMod q) * xy.2))
  left_inv := by
    intro xy
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · calc
        _ = (t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2)) * x := by
          simp only [gaussianResidueMul]; ring
        _ = x := by rw [ht]; ring
    · calc
        _ = (t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2)) * y := by
          simp only [gaussianResidueMul]; ring
        _ = y := by rw [ht]; ring

  right_inv := by
    intro xy
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · calc
        _ = (t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2)) * x := by
          simp only [gaussianResidueMul]; ring
        _ = x := by rw [ht]; ring
    · calc
        _ = (t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2)) * y := by
          simp only [gaussianResidueMul]; ring
        _ = y := by rw [ht]; ring

/-- The standard identification of two finite coordinates with two residues. -/
noncomputable def finResiduePairEquiv (q : ℕ) [NeZero q] :
    (Fin q × Fin q) ≃ (ZMod q × ZMod q) :=
  (ZMod.finEquiv q).toEquiv.prodCongr (ZMod.finEquiv q).toEquiv

/-- The Gaussian multiplication permutation transported to finite offsets. -/
noncomputable def gaussianFinResidueMulEquiv
    (q : ℕ) [NeZero q] (a : ℤ × ℤ) (t : ZMod q)
    (ht : t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2) = 1) :
    (Fin q × Fin q) ≃ (Fin q × Fin q) :=
  ((finResiduePairEquiv q).trans (gaussianResidueMulEquiv q a t ht)).trans
    (finResiduePairEquiv q).symm

/-- Cell offsets represent their integer coordinates modulo the period. -/
theorem finResiduePairEquiv_cellOffset
    (q : ℕ) [NeZero q] (p : ℤ × ℤ) :
    finResiduePairEquiv q (cellOffset q (NeZero.pos q) p) =
      ((p.1 : ZMod q), (p.2 : ZMod q)) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    simp only [finResiduePairEquiv, Equiv.prodCongr_apply]
    apply Prod.ext
    · apply ZMod.val_injective (n + 1)
      change (p.1 % (n + 1 : ℤ)).toNat = (p.1 : ZMod (n + 1)).val
      have hv : ((p.1 : ZMod (n + 1)).val : ℤ) =
          p.1 % (n + 1 : ℤ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ZMod.val_intCast (n := n + 1) p.1)
      omega
    · apply ZMod.val_injective (n + 1)
      change (p.2 % (n + 1 : ℤ)).toNat = (p.2 : ZMod (n + 1)).val
      have hv : ((p.2 : ZMod (n + 1)).val : ℤ) =
          p.2 % (n + 1 : ℤ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ZMod.val_intCast (n := n + 1) p.2)
      omega

/-- The finite permutation acts on offsets by Gaussian multiplication. -/
theorem gaussianFinResidueMulEquiv_apply
    (q : ℕ) [NeZero q] (a : ℤ × ℤ) (t : ZMod q)
    (ht : t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2) = 1)
    (uv : Fin q × Fin q) :
    gaussianFinResidueMulEquiv q a t ht uv =
      cellOffset q (NeZero.pos q)
        (gaussianPairMul a (signedCellPoint q 0 0 uv.1 uv.2)) := by
  let b := signedCellPoint q 0 0 uv.1 uv.2
  apply (finResiduePairEquiv q).injective
  have hb : finResiduePairEquiv q uv =
      ((b.1 : ZMod q), (b.2 : ZMod q)) := by
    simpa [b, cellOffset_signedCellPoint] using
      (finResiduePairEquiv_cellOffset q b)
  calc
    finResiduePairEquiv q (gaussianFinResidueMulEquiv q a t ht uv) =
        gaussianResidueMul q a (finResiduePairEquiv q uv) := by
      simp [gaussianFinResidueMulEquiv, gaussianResidueMulEquiv]
    _ = gaussianResidueMul q a ((b.1 : ZMod q), (b.2 : ZMod q)) := by rw [hb]
    _ = (((gaussianPairMul a b).1 : ZMod q),
          ((gaussianPairMul a b).2 : ZMod q)) := gaussianResidueMul_intCast q a b
    _ = finResiduePairEquiv q
          (cellOffset q (NeZero.pos q) (gaussianPairMul a b)) := by
      rw [finResiduePairEquiv_cellOffset]

/-- A Gaussian multiplier that permutes residue classes, together with a
nontrivial quartic value, makes the residue table have zero mean. -/
theorem residue_sum_zero_of_gaussian_multiplier
    (q : ℕ) (hq : 0 < q)
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (hperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι))
    (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight R ι a ≠ 1)
    (e : (Fin q × Fin q) ≃ (Fin q × Fin q))
    (he : ∀ uv,
      e uv = cellOffset q hq
        (gaussianPairMul a (signedCellPoint q 0 0 uv.1 uv.2))) :
    (∑ uv : Fin q × Fin q,
      residueWeight q (quarticIdealLatticeWeight R ι) uv) = 0 := by
  apply residue_sum_zero_of_eigenvalue q
    (residueWeight q (quarticIdealLatticeWeight R ι)) e
    (quarticIdealLatticeWeight R ι a) ha
  intro uv
  rw [he uv, ← periodic_weight_eq_residueWeight q hq _ hperiod]
  exact quarticIdealLatticeWeight_pairMul R ι a _

/-- A nontrivial Gaussian quartic value has zero residue mean whenever the
multiplier norm is invertible modulo a period. -/
theorem residue_sum_zero_of_unit_norm_multiplier
    (q : ℕ) [NeZero q]
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (hperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι))
    (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight R ι a ≠ 1)
    (t : ZMod q)
    (ht : t * ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2) = 1) :
    (∑ uv : Fin q × Fin q,
      residueWeight q (quarticIdealLatticeWeight R ι) uv) = 0 := by
  exact residue_sum_zero_of_gaussian_multiplier q (NeZero.pos q) R ι
    hperiod a ha (gaussianFinResidueMulEquiv q a t ht)
    (gaussianFinResidueMulEquiv_apply q a t ht)

/-- The inverse of the multiplier norm may be supplied as a unit proof. -/
theorem residue_sum_zero_of_isUnit_norm_multiplier
    (q : ℕ) [NeZero q]
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (hperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι))
    (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight R ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod q) ^ 2 + (a.2 : ZMod q) ^ 2)) :
    (∑ uv : Fin q × Fin q,
      residueWeight q (quarticIdealLatticeWeight R ι) uv) = 0 := by
  exact residue_sum_zero_of_unit_norm_multiplier q R ι hperiod a ha
    _ (ZMod.inv_mul_of_unit _ hunit)

/-- For a nonzero odd rational radicand, one nontrivial admissible Gaussian
multiplier gives the mean-zero condition used by the analytic L estimates. -/
theorem quarticIdealLatticeWeight_residue_mean_zero_of_multiplier
    (R : ℕ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R)) ^ 2 +
      (a.2 : ZMod (64 * R)) ^ 2)) :
    (∑ uv : Fin (64 * R) × Fin (64 * R),
      residueWeight (64 * R)
        (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι) uv) = 0 := by
  letI : NeZero (64 * R) := ⟨by omega⟩
  exact residue_sum_zero_of_isUnit_norm_multiplier (64 * R)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_periodic R hR0 hRodd ι) a ha hunit

/-- The concrete angular L bound once a nontrivial Gaussian multiplier is known. -/
theorem norm_quarticIdealAngularLSeries_le_log_of_multiplier
    (R : ℕ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R)) ^ 2 +
      (a.2 : ZMod (64 * R)) ^ 2))
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianWeightCoeff
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι)) (σ : ℂ)‖ ≤
      162 * Real.log (((64 * R : ℕ) : ℝ) ^ 2) + 648 := by
  letI : NeZero (64 * R) := ⟨by omega⟩
  exact norm_quarticIdealAngularLSeries_le_log (64 * R)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_periodic R hR0 hRodd ι)
    (quarticIdealLatticeWeight_residue_mean_zero_of_multiplier
      R hR0 hRodd ι a ha hunit) σ hσ₁ hσ₂

/-- The concrete infinity-type-zero L bound under the same witness. -/
theorem norm_quarticIdealZeroLSeries_le_log_of_multiplier
    (R : ℕ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R)) ^ 2 +
      (a.2 : ZMod (64 * R)) ^ 2))
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianZeroWeightCoeff
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι)) (σ : ℂ)‖ ≤
      162 * Real.log (((64 * R : ℕ) : ℝ) ^ 2) + 648 := by
  letI : NeZero (64 * R) := ⟨by omega⟩
  exact norm_quarticIdealZeroLSeries_le_log (64 * R)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_periodic R hR0 hRodd ι)
    (quarticIdealLatticeWeight_residue_mean_zero_of_multiplier
      R hR0 hRodd ι a ha hunit) σ hσ₁ hσ₂

/-- The same residue mean vanishes for a signed odd rational radicand. -/
theorem quarticIdealLatticeWeight_signed_residue_mean_zero_of_multiplier
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2)) :
    (∑ uv : Fin (64 * R.natAbs) × Fin (64 * R.natAbs),
      residueWeight (64 * R.natAbs)
        (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι) uv) = 0 := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  exact residue_sum_zero_of_isUnit_norm_multiplier (64 * R.natAbs)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_signed_odd_periodic R hR0 hRodd ι)
    a ha hunit

/-- The angular L bound for a signed odd radicand and a nontrivial multiplier. -/
theorem norm_quarticIdealAngularLSeries_le_log_of_signed_multiplier
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianWeightCoeff
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι)) (σ : ℂ)‖ ≤
      162 * Real.log (((64 * R.natAbs : ℕ) : ℝ) ^ 2) + 648 := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  exact norm_quarticIdealAngularLSeries_le_log (64 * R.natAbs)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_signed_odd_periodic R hR0 hRodd ι)
    (quarticIdealLatticeWeight_signed_residue_mean_zero_of_multiplier
      R hR0 hRodd ι a ha hunit) σ hσ₁ hσ₂

/-- The infinity-type-zero L bound for the same signed odd radicand. -/
theorem norm_quarticIdealZeroLSeries_le_log_of_signed_multiplier
    (R : ℤ) (hR0 : R ≠ 0) (hRodd : Odd R)
    (ι : GaussianField →+* ℂ) (a : ℤ × ℤ)
    (ha : quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι a ≠ 1)
    (hunit : IsUnit ((a.1 : ZMod (64 * R.natAbs)) ^ 2 +
      (a.2 : ZMod (64 * R.natAbs)) ^ 2))
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianZeroWeightCoeff
      (quarticIdealLatticeWeight (R : 𝓞 GaussianField) ι)) (σ : ℂ)‖ ≤
      162 * Real.log (((64 * R.natAbs : ℕ) : ℝ) ^ 2) + 648 := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  exact norm_quarticIdealZeroLSeries_le_log (64 * R.natAbs)
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_signed_odd_periodic R hR0 hRodd ι)
    (quarticIdealLatticeWeight_signed_residue_mean_zero_of_multiplier
      R hR0 hRodd ι a ha hunit) σ hσ₁ hσ₂

end Erdos940.Quartic.GaussianZeroMean
