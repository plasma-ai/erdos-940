import Erdos940.Quartic.FixedParts
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volume of a positive quartic ball

The fixed-coefficient lattice count in `FixedParts` uses the volume of a
positive quartic ball. This file evaluates that volume and separates the
coefficient scaling from the unit ball calculation.
-/

namespace Erdos940.Quartic

open MeasureTheory

/-- Rescaling the four coordinates by the positive fourth roots of their
coefficients reduces the region to the unit-coefficient region. -/
theorem fixedPartVolume_eq_unit_mul_weight (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) :
    fixedPartVolume d =
      fixedPartVolume (fun _ => 1) *
        ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ)) := by
  classical
  let s : Fin 4 → ℝ := fun i => (d i : ℝ) ^ (1 / 4 : ℝ)
  let L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    (Matrix.diagonal s).toLin'
  have hspos (i : Fin 4) : 0 < s i := by
    dsimp [s]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hd i) _
  have hspow (i : Fin 4) : (s i) ^ 4 = (d i : ℝ) := by
    dsimp [s]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg (d i)) (1 / 4 : ℝ) 4]
    norm_num
  have hL (x : Fin 4 → ℝ) (i : Fin 4) : L x i = s i * x i := by
    simp [L, Matrix.mulVec_diagonal]
  have hsum (x : Fin 4 → ℝ) :
      (∑ i, ((1 : ℕ) : ℝ) * (L x i) ^ 4) =
        ∑ i, (d i : ℝ) * (x i) ^ 4 := by
    simp only [Nat.cast_one, one_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hL, mul_pow, hspow]
  have hpre : quarticRegion d =
      L ⁻¹' quarticRegion (fun _ => 1) := by
    ext x
    change ((∀ i, 0 ≤ x i) ∧
        (∑ i, (d i : ℝ) * (x i) ^ 4) ≤ 1) ↔
      ((∀ i, 0 ≤ L x i) ∧
        (∑ i, ((1 : ℕ) : ℝ) * (L x i) ^ 4) ≤ 1)
    rw [hsum]
    constructor
    · rintro ⟨hx, hbound⟩
      exact ⟨fun i => by rw [hL]; exact mul_nonneg (hspos i).le (hx i), hbound⟩
    · rintro ⟨hx, hbound⟩
      refine ⟨fun i => ?_, hbound⟩
      have hi : 0 ≤ s i * x i := by rw [← hL]; exact hx i
      exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hi) (hspos i)
  have hdet : LinearMap.det L = ∏ i, s i := by
    simp [L, Matrix.det_diagonal]
  have hdetpos : 0 < LinearMap.det L := by
    rw [hdet]
    exact Finset.prod_pos (fun i _ => hspos i)
  have hcoef :
      abs (LinearMap.det L)⁻¹ =
        ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [hdet, abs_of_pos (inv_pos.mpr (hdet ▸ hdetpos))]
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact (Real.rpow_neg (Nat.cast_nonneg (d i)) (1 / 4 : ℝ)).symm
  have hmap :
      MeasureTheory.volume (quarticRegion d) =
        ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
          MeasureTheory.volume (quarticRegion (fun _ => 1)) := by
    calc
      MeasureTheory.volume (quarticRegion d) =
          (Measure.map L MeasureTheory.volume)
            (quarticRegion (fun _ => 1)) := by
        rw [Measure.map_apply
          ((LinearMap.continuous_on_pi L).measurable)
          (quarticRegion_measurableSet _)]
        rw [← hpre]
      _ = _ := by
        rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdetpos.ne']
        rfl
  unfold fixedPartVolume
  change (MeasureTheory.volume (quarticRegion d)).toReal =
    (MeasureTheory.volume (quarticRegion (fun _ => 1))).toReal *
      ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ))
  rw [hmap, hcoef, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  ring

private def quarticBall : Set (Fin 4 → ℝ) :=
  {x | (∑ i, (x i) ^ 4) ≤ 1}

private theorem quarticBall_volume :
    volume quarticBall =
      ENNReal.ofReal (16 * Real.Gamma (5 / 4 : ℝ) ^ 4) := by
  have hset :
      {x : Fin 4 → ℝ |
        (∑ i, |x i| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) ≤ 1} =
        quarticBall := by
    ext x
    have hnonneg : 0 ≤ (∑ i, |x i| ^ (4 : ℝ)) := by positivity
    have hiff :
        (∑ i, |x i| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) ≤ 1 ↔
          (∑ i, |x i| ^ (4 : ℝ)) ≤ 1 := by
      simpa using (Real.rpow_le_rpow_iff hnonneg
        (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) < 1 / 4))
    simpa [quarticBall, Real.rpow_natCast,
      Even.pow_abs (by decide : Even (4 : ℕ))] using hiff
  rw [← hset, MeasureTheory.volume_sum_rpow_le (Fin 4)
    (p := (4 : ℝ)) (by norm_num) 1]
  norm_num [Real.Gamma_nat_eq_factorial]
  have hring : (2 * Real.Gamma (5 / 4 : ℝ)) ^ 4 =
      16 * Real.Gamma (5 / 4 : ℝ) ^ 4 := by ring
  rw [hring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

private def coordinateHyperplanes : Set (Fin 4 → ℝ) :=
  ⋃ i : Fin 4, {x | x i = 0}

private theorem coordinateHyperplanes_null :
    volume coordinateHyperplanes = 0 := by
  unfold coordinateHyperplanes
  apply measure_iUnion_null
  intro i
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ : Fin 4 => volume) i 0

private def strictQuarticOrthant (σ : Fin 4 → Bool) : Set (Fin 4 → ℝ) :=
  {x | x ∈ quarticBall ∧ ∀ i, if σ i then 0 < x i else x i < 0}

private theorem strictQuarticOrthant_measurable (σ : Fin 4 → Bool) :
    MeasurableSet (strictQuarticOrthant σ) := by
  have hc : Continuous (fun x : Fin 4 → ℝ => ∑ i, (x i) ^ 4) := by
    fun_prop
  have hball : MeasurableSet quarticBall := by
    exact hc.measurable measurableSet_Iic
  have horth : IsOpen {x : Fin 4 → ℝ |
      ∀ i, if σ i then 0 < x i else x i < 0} := by
    have hset : {x : Fin 4 → ℝ |
        ∀ i, if σ i then 0 < x i else x i < 0} =
        Set.univ.pi
          (fun i : Fin 4 => if σ i then Set.Ioi (0 : ℝ) else Set.Iio 0) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro hx i
        by_cases hi : σ i <;> simpa [hi] using hx i
      · intro hx i
        by_cases hi : σ i <;> simpa [hi] using hx i
    rw [hset]
    exact isOpen_set_pi Set.finite_univ (fun i _ => by
      by_cases hi : σ i <;> simp [hi, isOpen_Ioi, isOpen_Iio])
  exact hball.inter horth.measurableSet

private def signFlip (σ : Fin 4 → Bool) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => if σ i then x i else -x i

private theorem signFlip_volumePreserving (σ : Fin 4 → Bool) :
    MeasurePreserving (signFlip σ) := by
  have h : MeasurePreserving
      (fun a : Fin 4 → ℝ => fun i =>
        (if σ i then (id : ℝ → ℝ) else fun x => -x) (a i)) := by
    apply volume_preserving_pi
    intro i
    by_cases hi : σ i
    · simpa [hi] using (MeasurePreserving.id (volume : Measure ℝ))
    · simpa [hi] using (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hfun :
      (fun a : Fin 4 → ℝ => fun i =>
        (if σ i then (id : ℝ → ℝ) else fun x => -x) (a i)) = signFlip σ := by
    funext a i
    by_cases hi : σ i <;> simp [signFlip, hi]
  exact hfun ▸ h

private theorem strictQuarticOrthant_eq_preimage (σ : Fin 4 → Bool) :
    strictQuarticOrthant σ =
      signFlip σ ⁻¹' strictQuarticOrthant (fun _ => true) := by
  have hsum (x : Fin 4 → ℝ) :
      (∑ i, (signFlip σ x i) ^ 4) = ∑ i, (x i) ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : σ i
    · simp [signFlip, hi]
    · simp [signFlip, hi]
      ring
  ext x
  change (x ∈ quarticBall ∧ ∀ i, if σ i then 0 < x i else x i < 0) ↔
    (signFlip σ x ∈ quarticBall ∧
      ∀ i, if true then 0 < signFlip σ x i else signFlip σ x i < 0)
  simp only [ite_true]
  constructor
  · rintro ⟨hball, horth⟩
    constructor
    · simpa [quarticBall, hsum] using hball
    · intro i
      by_cases hi : σ i
      · simpa [signFlip, hi] using horth i
      · simpa [signFlip, hi] using horth i
  · rintro ⟨hball, horth⟩
    constructor
    · simpa [quarticBall, hsum] using hball
    · intro i
      by_cases hi : σ i
      · simpa [signFlip, hi] using horth i
      · simpa [signFlip, hi] using horth i

private theorem strictQuarticOrthant_volume_eq (σ : Fin 4 → Bool) :
    volume (strictQuarticOrthant σ) =
      volume (strictQuarticOrthant (fun _ => true)) := by
  rw [strictQuarticOrthant_eq_preimage]
  rw [← Measure.map_apply (signFlip_volumePreserving σ).measurable
    (strictQuarticOrthant_measurable _)]
  rw [(signFlip_volumePreserving σ).map_eq]

private theorem quarticBall_volume_eq_orthant :
    volume quarticBall =
      16 * volume (strictQuarticOrthant (fun _ => true)) := by
  let U : Set (Fin 4 → ℝ) :=
    ⋃ σ : Fin 4 → Bool, strictQuarticOrthant σ
  have hcover : quarticBall \ coordinateHyperplanes ⊆ U := by
    intro x hx
    have hnonzero (i : Fin 4) : x i ≠ 0 := by
      intro hz
      exact hx.2 (show x ∈ coordinateHyperplanes by
        unfold coordinateHyperplanes
        exact Set.mem_iUnion.mpr ⟨i, hz⟩)
    let σ : Fin 4 → Bool := fun i => decide (0 < x i)
    change x ∈ ⋃ σ : Fin 4 → Bool, strictQuarticOrthant σ
    refine Set.mem_iUnion.mpr ⟨σ, hx.1, fun i => ?_⟩
    by_cases hi : 0 < x i
    · simp [σ, hi]
    · have hneg : x i < 0 :=
        lt_of_le_of_ne (le_of_not_gt hi) (hnonzero i)
      simp [σ, hi, hneg]
  have hsub : U ⊆ quarticBall := by
    intro x hx
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
    exact hσ.1
  have hdiff : quarticBall \ U ⊆ coordinateHyperplanes := by
    intro x hx
    by_contra hnot
    exact hx.2 (hcover ⟨hx.1, hnot⟩)
  have hU : volume U = volume quarticBall :=
    measure_eq_measure_of_null_sdiff hsub
      (measure_mono_null hdiff coordinateHyperplanes_null)
  have hdisjoint :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 4 → Bool)))
        strictQuarticOrthant := by
    intro σ _ τ _ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    change x ∈ quarticBall ∧
      (∀ i, if σ i then 0 < x i else x i < 0) at hx
    change x ∈ quarticBall ∧
      (∀ i, if τ i then 0 < x i else x i < 0) at hy
    have heq (i : Fin 4) : σ i = τ i := by
      by_cases hσ : σ i
      · by_cases hτ : τ i
        · simp [hσ, hτ]
        · have hp : 0 < x i := by simpa [hσ] using hx.2 i
          have hn : x i < 0 := by simpa [hτ] using hy.2 i
          linarith
      · by_cases hτ : τ i
        · have hn : x i < 0 := by simpa [hσ] using hx.2 i
          have hp : 0 < x i := by simpa [hτ] using hy.2 i
          linarith
        · simp [hσ, hτ]
    exact hne (funext heq)
  have hsum : volume U =
      ∑ σ : Fin 4 → Bool, volume (strictQuarticOrthant σ) := by
    simpa [U] using
      (measure_biUnion_finset hdisjoint
        (fun σ _ => strictQuarticOrthant_measurable σ))
  calc
    volume quarticBall = volume U := hU.symm
    _ = ∑ σ : Fin 4 → Bool, volume (strictQuarticOrthant σ) := hsum
    _ = 16 * volume (strictQuarticOrthant (fun _ => true)) := by
      simp_rw [strictQuarticOrthant_volume_eq]
      simp

/-- The closed positive region and its strictly positive part differ only on
coordinate hyperplanes. -/
private theorem unitRegion_volume_eq_strictOrthant :
    volume (quarticRegion (fun _ => 1)) =
      volume (strictQuarticOrthant (fun _ => true)) := by
  have hsub :
      strictQuarticOrthant (fun _ => true) ⊆
        quarticRegion (fun _ => 1) := by
    intro x hx
    change x ∈ quarticBall ∧
      (∀ i, if true then 0 < x i else x i < 0) at hx
    change (∀ i, 0 ≤ x i) ∧
      (∑ i, ((1 : ℕ) : ℝ) * (x i) ^ 4) ≤ 1
    exact ⟨fun i => (by simpa using hx.2 i : 0 < x i).le,
      by simpa [quarticBall] using hx.1⟩
  have hdiff :
      quarticRegion (fun _ => 1) \
        strictQuarticOrthant (fun _ => true) ⊆
          coordinateHyperplanes := by
    intro x hx
    have hpos : ∀ i, 0 ≤ x i := hx.1.1
    have hnot : ¬∀ i, 0 < x i := by
      intro hp
      apply hx.2
      change x ∈ quarticBall ∧
        (∀ i, if true then 0 < x i else x i < 0)
      exact ⟨by simpa [quarticBall] using hx.1.2,
        by simpa using hp⟩
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hzero : x i = 0 :=
      le_antisymm (le_of_not_gt hi) (hpos i)
    unfold coordinateHyperplanes
    exact Set.mem_iUnion.mpr ⟨i, hzero⟩
  exact (measure_eq_measure_of_null_sdiff hsub
    (measure_mono_null hdiff coordinateHyperplanes_null)).symm

/-- The unit positive quartic ball has volume Γ(5/4)⁴. -/
theorem unitQuarticVolume_eq_gamma :
    fixedPartVolume (fun _ : Fin 4 => 1) =
      Real.Gamma (5 / 4 : ℝ) ^ 4 := by
  have hball := quarticBall_volume
  rw [quarticBall_volume_eq_orthant,
    ← unitRegion_volume_eq_strictOrthant] at hball
  have hreal := congrArg ENNReal.toReal hball
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 16 * Real.Gamma (5 / 4 : ℝ) ^ 4)] at hreal
  simpa [fixedPartVolume, MeasureTheory.Measure.real] using hreal

/-- Explicit leading volume in the fixed-coefficient lattice count. -/
theorem fixedPartVolume_eq_gamma_weight (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) :
    fixedPartVolume d =
      Real.Gamma (5 / 4 : ℝ) ^ 4 *
        ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ)) := by
  rw [fixedPartVolume_eq_unit_mul_weight d hd,
    unitQuarticVolume_eq_gamma]

/-- Equation (4) of the quartic complement proof in limit form. -/
theorem fixedPartCount_asymptotic_gamma (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M a : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun X : ℕ => (fixedPartCount d M a X : ℝ) / (X : ℝ))
      Filter.atTop
      (nhds ((Real.Gamma (5 / 4 : ℝ) ^ 4 *
        ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ))) *
          (localCount d M a : ℝ) / (M : ℝ) ^ 4)) := by
  simpa only [fixedPartVolume_eq_gamma_weight d hd] using
    fixedPartCount_asymptotic d hd M a

/-- Equation (5) of the quartic complement proof, for ordered representations
by exactly four positive 4-powerful summands. -/
theorem firstMoment_asymptotic_gamma (M a : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun X : ℕ => ∑' d : Fin 4 → CanonicalParts,
        (fixedPartCount (fun i => (d i).val) M a X : ℝ) / (X : ℝ))
      Filter.atTop
      (nhds (∑' d : Fin 4 → CanonicalParts,
        (Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4)) := by
  have hlimit :
      (∑' d : Fin 4 → CanonicalParts,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) =
      (∑' d : Fin 4 → CanonicalParts,
        (Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) := by
    apply tsum_congr
    intro d
    rw [fixedPartVolume_eq_gamma_weight (fun i => (d i).val)
      (fun i => (d i).property.pos)]
    rfl
  rw [← hlimit]
  exact firstMoment_asymptotic M a

end Erdos940.Quartic
