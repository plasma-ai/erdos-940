import Erdos940.Quartic.CanonicalParts
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Counting four fourth powers with fixed canonical coefficients

The definitions here use an ordered quadruple of positive fourth-power roots.
They formalize the fixed-coefficient count in equation (4) of the quartic
complement proof. Each coefficient will range over canonical 4-powerful parts.

The region's regularity, ordinary-grid lattice limit, residue-vector limit,
and fixed-parts asymptotic are proved here.
-/

namespace Erdos940.Quartic

open scoped Pointwise

/-- The integer represented by four fixed coefficients and fourth-power roots. -/
def quarticForm (d x : Fin 4 → ℕ) : ℕ :=
  ∑ i, d i * (x i) ^ 4

/-- The same quartic form over `ZMod M`. -/
def quarticFormMod (M : ℕ) (d : Fin 4 → ℕ) (x : Fin 4 → ZMod M) : ZMod M :=
  ∑ i, (d i : ZMod M) * (x i) ^ 4

theorem quarticForm_cast (M : ℕ) (d x : Fin 4 → ℕ) :
    (quarticForm d x : ZMod M) = quarticFormMod M d (fun i => (x i : ZMod M)) := by
  simp [quarticForm, quarticFormMod]

/-- A positive quartic root does not exceed the represented integer. -/
theorem quarticForm_coord_le (d x : Fin 4 → ℕ) (hd : ∀ i, 0 < d i)
    (i : Fin 4) : x i ≤ quarticForm d x := by
  by_cases hx : x i = 0
  · simp [hx]
  have hxi : 0 < x i := Nat.pos_of_ne_zero hx
  calc
    x i ≤ (x i) ^ 4 := le_self_pow (Nat.one_le_iff_ne_zero.mpr hxi.ne') (by decide)
    _ ≤ d i * (x i) ^ 4 := le_mul_of_one_le_left (Nat.zero_le _) (hd i)
    _ ≤ quarticForm d x := by
      unfold quarticForm
      exact Finset.single_le_sum (f := fun j : Fin 4 => d j * (x j) ^ 4)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem quarticForm_mono (d : Fin 4 → ℕ) {x y : Fin 4 → ℕ}
    (hxy : x ≤ y) : quarticForm d x ≤ quarticForm d y := by
  unfold quarticForm
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (pow_le_pow_left₀ (Nat.zero_le _) (hxy i) 4)

private theorem quarticForm_nsmul (d x : Fin 4 → ℕ) (M : ℕ) :
    quarticForm d (fun i => M * x i) = M ^ 4 * quarticForm d x := by
  simp only [quarticForm, mul_pow]
  rw [Finset.mul_sum]
  congr 1
  ext i
  ring

/-- Positive ordered quadruples of fourth-power roots with a bounded sum in one residue
class. The roots are represented by `Fin (X+1)` because every positive root
of a sum at most `X` is itself at most `X` when all coefficients are positive. -/
noncomputable def fixedPartCount (d : Fin 4 → ℕ) (M a X : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : Fin 4 → Fin (X + 1) //
    (∀ i, 0 < (x i).val) ∧
    quarticForm d (fun i => (x i).val) ≤ X ∧
    (quarticForm d (fun i => (x i).val) : ZMod M) = (a : ZMod M)}

/-- The number of admissible residue vectors modulo a positive modulus. -/
noncomputable def localCount (d : Fin 4 → ℕ) (M a : ℕ) [NeZero M] : ℕ := by
  classical
  exact Fintype.card {x : Fin 4 → ZMod M // quarticFormMod M d x = (a : ZMod M)}

/-- Positive lattice points in one fixed vector of residue classes. -/
noncomputable def residueVectorCount (d : Fin 4 → ℕ) (M X : ℕ)
    (r : Fin 4 → ZMod M) : ℕ := by
  classical
  exact Fintype.card {x : Fin 4 → Fin (X + 1) //
    (∀ i, 0 < (x i).val) ∧
    quarticForm d (fun i => (x i).val) ≤ X ∧
    (∀ i, ((x i).val : ZMod M) = r i)}

/-- The same residue-vector count without a cutoff in the coordinate type.
This form is convenient when passing to a translated integer grid. -/
noncomputable def residueNatCount (d : Fin 4 → ℕ) (M X : ℕ)
    (r : Fin 4 → ZMod M) : ℕ :=
  Nat.card {x : Fin 4 → ℕ //
    (∀ i, 0 < x i) ∧ quarticForm d x ≤ X ∧
    (∀ i, (x i : ZMod M) = r i)}

theorem residueVectorCount_eq_residueNatCount (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M X : ℕ) (r : Fin 4 → ZMod M) :
    residueVectorCount d M X r = residueNatCount d M X r := by
  classical
  let e : {x : Fin 4 → Fin (X + 1) //
      (∀ i, 0 < (x i).val) ∧
      quarticForm d (fun i => (x i).val) ≤ X ∧
      (∀ i, ((x i).val : ZMod M) = r i)} ≃
      {x : Fin 4 → ℕ //
        (∀ i, 0 < x i) ∧ quarticForm d x ≤ X ∧
        (∀ i, (x i : ZMod M) = r i)} :=
    { toFun := fun x => ⟨fun i => (x.val i).val, x.property⟩
      invFun := fun x => ⟨fun i => ⟨x.val i,
          Nat.lt_succ_of_le ((quarticForm_coord_le d x.val hd i).trans
            x.property.2.1)⟩, x.property⟩
      left_inv := by intro x; apply Subtype.ext; funext i; apply Fin.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  unfold residueVectorCount residueNatCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr e

/-- Parameterization of a fixed residue class by its quotient coordinates. -/
noncomputable def translatedResidueCount (d : Fin 4 → ℕ) (M X : ℕ)
    (r : Fin 4 → ZMod M) : ℕ :=
  Nat.card {k : Fin 4 → ℕ //
    (∀ i, 0 < (r i).val + M * k i) ∧
    quarticForm d (fun i => (r i).val + M * k i) ≤ X}

theorem residueNatCount_eq_translatedResidueCount (d : Fin 4 → ℕ)
    (M X : ℕ) [NeZero M] (r : Fin 4 → ZMod M) :
    residueNatCount d M X r = translatedResidueCount d M X r := by
  classical
  let fromK : (Fin 4 → ℕ) → (Fin 4 → ℕ) :=
    fun k i => (r i).val + M * k i
  have hcast (k : Fin 4 → ℕ) (i : Fin 4) :
      (fromK k i : ZMod M) = r i := by
    simp [fromK, ZMod.natCast_val]
  have hrepr (x : Fin 4 → ℕ) (hx : ∀ i, (x i : ZMod M) = r i) (i : Fin 4) :
      fromK (fun i => x i / M) i = x i := by
    have hmod : x i % M = (r i).val := by
      have h := congrArg ZMod.val (hx i)
      simpa [ZMod.val_natCast] using h
    simpa [fromK, ← hmod] using Nat.mod_add_div (x i) M
  let e : {x : Fin 4 → ℕ //
      (∀ i, 0 < x i) ∧ quarticForm d x ≤ X ∧
      (∀ i, (x i : ZMod M) = r i)} ≃
      {k : Fin 4 → ℕ //
        (∀ i, 0 < (r i).val + M * k i) ∧
        quarticForm d (fun i => (r i).val + M * k i) ≤ X} :=
    { toFun := fun x => ⟨fun i => x.val i / M, by
        have heq : fromK (fun i => x.val i / M) = x.val :=
          funext (hrepr x.val x.property.2.2)
        change (∀ i, 0 < fromK (fun i => x.val i / M) i) ∧
          quarticForm d (fromK (fun i => x.val i / M)) ≤ X
        rw [heq]
        exact ⟨x.property.1, x.property.2.1⟩⟩
      invFun := fun k => ⟨fromK k, ⟨k.property.1, k.property.2, hcast k.val⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact funext (hrepr x.val x.property.2.2)
      right_inv := by
        intro k
        apply Subtype.ext
        funext i
        change ((r i).val + M * k.val i) / M = k.val i
        rw [Nat.add_mul_div_left _ _ (NeZero.pos M), Nat.div_eq_of_lt (r i).val_lt]
        exact Nat.zero_add _
    }
  unfold residueNatCount translatedResidueCount
  exact Nat.card_congr e

/-- Choose the representative in `{1,…,M}`, taking `M` for the zero class. -/
private def positiveResidueRep (M : ℕ) [NeZero M] (r : ZMod M) : ℕ :=
  if r.val = 0 then M else r.val

private theorem positiveResidueRep_pos (M : ℕ) [NeZero M] (r : ZMod M) :
    0 < positiveResidueRep M r := by
  unfold positiveResidueRep
  split_ifs with h
  · exact NeZero.pos M
  · exact Nat.pos_of_ne_zero h

private theorem positiveResidueRep_le (M : ℕ) [NeZero M] (r : ZMod M) :
    positiveResidueRep M r ≤ M := by
  unfold positiveResidueRep
  split_ifs
  · exact le_rfl
  · exact (r.val_lt).le

private theorem positiveResidueRep_cast (M : ℕ) [NeZero M] (r : ZMod M) :
    (positiveResidueRep M r : ZMod M) = r := by
  unfold positiveResidueRep
  split_ifs with h
  · have hr0 : r = 0 := by
      have hv := ZMod.natCast_zmod_val r
      simpa [h] using hv.symm
    simp [hr0]
  · exact ZMod.natCast_zmod_val r

private theorem exists_positiveResidueRep (M : ℕ) [NeZero M] (r : ZMod M)
    (x : ℕ) (hx : 0 < x) (hr : (x : ZMod M) = r) :
    ∃ k : ℕ, x = positiveResidueRep M r + M * k := by
  have hmod : x % M = r.val := by
    have h := congrArg ZMod.val hr
    simpa [ZMod.val_natCast] using h
  by_cases hzero : r.val = 0
  · have hxmul : x = M * (x / M) := by
      simpa [hmod, hzero] using (Nat.mod_add_div x M).symm
    have hq : 0 < x / M := by
      by_contra hq
      have : x / M = 0 := Nat.eq_zero_of_not_pos hq
      simp [this] at hxmul
      omega
    refine ⟨x / M - 1, ?_⟩
    simp only [positiveResidueRep, hzero, ↓reduceIte]
    have hqeq : x / M = (x / M - 1) + 1 := by omega
    calc
      x = M * (x / M) := hxmul
      _ = M * ((x / M - 1) + 1) := by rw [← hqeq]
      _ = M + M * (x / M - 1) := by simp [Nat.mul_add, add_comm]
  · refine ⟨x / M, ?_⟩
    simp only [positiveResidueRep, hzero, ↓reduceIte]
    rw [← hmod]
    exact (Nat.mod_add_div x M).symm

/-- Positive representatives make every shifted quotient vector positive,
including the zero residue class. -/
noncomputable def translatedPositiveResidueCount (d : Fin 4 → ℕ) (M X : ℕ)
    [NeZero M] (r : Fin 4 → ZMod M) : ℕ :=
  Nat.card {k : Fin 4 → ℕ //
    quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X}

theorem residueNatCount_eq_translatedPositiveResidueCount (d : Fin 4 → ℕ)
    (M X : ℕ) [NeZero M] (r : Fin 4 → ZMod M) :
    residueNatCount d M X r = translatedPositiveResidueCount d M X r := by
  classical
  let rep : Fin 4 → ℕ := fun i => positiveResidueRep M (r i)
  let fromK : (Fin 4 → ℕ) → (Fin 4 → ℕ) := fun k i => rep i + M * k i
  have hcast (k : Fin 4 → ℕ) (i : Fin 4) : (fromK k i : ZMod M) = r i := by
    simp [fromK, rep, positiveResidueRep_cast]
  have hpos (k : Fin 4 → ℕ) (i : Fin 4) : 0 < fromK k i := by
    exact (positiveResidueRep_pos M (r i)).trans_le (Nat.le_add_right _ _)
  have hrepr (x : Fin 4 → ℕ) (hx : ∀ i, 0 < x i)
      (hr : ∀ i, (x i : ZMod M) = r i) :
      ∃ k : Fin 4 → ℕ, fromK k = x := by
    choose k hk using fun i => exists_positiveResidueRep M (r i) (x i) (hx i) (hr i)
    exact ⟨k, funext fun i => (hk i).symm⟩
  choose toK htoK using fun x : {x : Fin 4 → ℕ //
      (∀ i, 0 < x i) ∧ quarticForm d x ≤ X ∧
      (∀ i, (x i : ZMod M) = r i)} =>
    hrepr x.val x.property.1 x.property.2.2
  let e : {x : Fin 4 → ℕ //
      (∀ i, 0 < x i) ∧ quarticForm d x ≤ X ∧
      (∀ i, (x i : ZMod M) = r i)} ≃
      {k : Fin 4 → ℕ //
        quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X} :=
    { toFun := fun x => ⟨toK x, by
        change quarticForm d (fromK (toK x)) ≤ X
        rw [htoK x]
        exact x.property.2.1⟩
      invFun := fun k => ⟨fromK k.val,
        ⟨hpos k.val, k.property, hcast k.val⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact htoK x
      right_inv := by
        intro k
        apply Subtype.ext
        funext i
        have hi := congrArg (fun f : Fin 4 → ℕ => f i) (htoK
          ⟨fromK k.val, ⟨hpos k.val, k.property, hcast k.val⟩⟩)
        change rep i + M * toK _ i = rep i + M * k.val i at hi
        exact Nat.mul_left_cancel (NeZero.pos M) (Nat.add_left_cancel hi) }
  unfold residueNatCount translatedPositiveResidueCount
  exact Nat.card_congr e

theorem fixedPartCount_le_box (d : Fin 4 → ℕ) (M a X : ℕ) :
    fixedPartCount d M a X ≤ Fintype.card (Fin 4 → Fin (X + 1)) := by
  classical
  unfold fixedPartCount
  exact Fintype.card_subtype_le _

theorem localCount_le_box (d : Fin 4 → ℕ) (M a : ℕ) [NeZero M] :
    localCount d M a ≤ Fintype.card (Fin 4 → ZMod M) := by
  classical
  unfold localCount
  exact Fintype.card_subtype_le _

/-- The positive-octant quartic region for fixed coefficients. -/
def quarticRegion (d : Fin 4 → ℕ) : Set (Fin 4 → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ (∑ i, (d i : ℝ) * (t i) ^ 4) ≤ 1}

/-- Its volume, which is the leading constant in the fixed-parts count. -/
noncomputable def fixedPartVolume (d : Fin 4 → ℕ) : ℝ :=
  MeasureTheory.volume.real (quarticRegion d)

theorem quarticRegion_subset_unitBox (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    quarticRegion d ⊆ Set.Icc (0 : Fin 4 → ℝ) 1 := by
  intro t ht
  constructor
  · exact ht.1
  · intro i
    have hnonneg (j : Fin 4) : 0 ≤ (d j : ℝ) * (t j) ^ 4 :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ht.1 j) _)
    have hterm : (d i : ℝ) * (t i) ^ 4 ≤ (1 : ℝ) :=
      (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)).trans ht.2
    have hcoef : (1 : ℝ) ≤ d i := by exact_mod_cast hd i
    have hquartic : (t i) ^ 4 ≤ (1 : ℝ) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hcoef) (pow_nonneg (ht.1 i) 4)
      nlinarith
    exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by norm_num) (by simpa using hquartic)

theorem quarticRegion_isBounded (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    Bornology.IsBounded (quarticRegion d) :=
  (Metric.isBounded_Icc (0 : Fin 4 → ℝ) 1).subset (quarticRegion_subset_unitBox d hd)

theorem quarticRegion_measurableSet (d : Fin 4 → ℕ) :
    MeasurableSet (quarticRegion d) := by
  have hc : Continuous (fun t : Fin 4 → ℝ => ∑ i, (d i : ℝ) * (t i) ^ 4) := by
    fun_prop
  change MeasurableSet
    (Set.Ici (0 : Fin 4 → ℝ) ∩
      (fun t : Fin 4 → ℝ => ∑ i, (d i : ℝ) * (t i) ^ 4) ⁻¹' Set.Iic 1)
  exact measurableSet_Ici.inter (hc.measurable measurableSet_Iic)

theorem quarticRegion_convex (d : Fin 4 → ℕ) : Convex ℝ (quarticRegion d) := by
  let P : Set (Fin 4 → ℝ) := Set.Ici 0
  have hP : Convex ℝ P := convex_Ici _
  have hi (i : Fin 4) :
      ConvexOn ℝ P (fun t : Fin 4 → ℝ => (d i : ℝ) * (t i) ^ 4) := by
    refine ⟨hP, ?_⟩
    intro x hx y hy a b ha hb hab
    have hpow := (convexOn_pow (𝕜 := ℝ) 4).2 (hx i) (hy i) ha hb hab
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hpow ⊢
    calc
      (d i : ℝ) * (a * x i + b * y i) ^ 4
          ≤ (d i : ℝ) * (a * (x i) ^ 4 + b * (y i) ^ 4) :=
            mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = a * ((d i : ℝ) * (x i) ^ 4) +
            b * ((d i : ℝ) * (y i) ^ 4) := by ring
  have hf :
      ConvexOn ℝ P (fun t : Fin 4 → ℝ => ∑ i, (d i : ℝ) * (t i) ^ 4) := by
    refine ⟨hP, ?_⟩
    intro x hx y hy a b ha hb hab
    calc
      (∑ i, (d i : ℝ) * ((a • x + b • y) i) ^ 4)
          ≤ ∑ i, (a * ((d i : ℝ) * (x i) ^ 4) +
              b * ((d i : ℝ) * (y i) ^ 4)) := by
            apply Finset.sum_le_sum
            intro i _
            simpa only [smul_eq_mul] using (hi i).2 hx hy ha hb hab
      _ = a • (∑ i, (d i : ℝ) * (x i) ^ 4) +
          b • (∑ i, (d i : ℝ) * (y i) ^ 4) := by
            simp [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
  change Convex ℝ {t ∈ P | (∑ i, (d i : ℝ) * (t i) ^ 4) ≤ 1}
  exact hf.convex_le 1

theorem quarticRegion_frontier_null (d : Fin 4 → ℕ) :
    MeasureTheory.volume (frontier (quarticRegion d)) = 0 :=
  Convex.addHaar_frontier MeasureTheory.volume (quarticRegion_convex d)

/-- Within the positive orthant, the quartic region is downward closed in each
coordinate. This gives the lower and upper integer-grid squeeze for residue
vectors. -/
theorem quarticRegion_downward (d : Fin 4 → ℕ) {x y : Fin 4 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : x ≤ y) (hy : y ∈ quarticRegion d) :
    x ∈ quarticRegion d := by
  refine ⟨hx, ?_⟩
  calc
    (∑ i, (d i : ℝ) * (x i) ^ 4)
        ≤ ∑ i, (d i : ℝ) * (y i) ^ 4 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hx i) (hxy i) 4) (Nat.cast_nonneg _)
    _ ≤ 1 := hy.2

theorem fixedPartVolume_pos (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    0 < fixedPartVolume d := by
  let S : ℕ := ∑ i, d i
  let c : ℝ := 1 / ((S : ℝ) + 1)
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (S : ℝ) + 1)).mpr
    linarith
  have hbox : Set.Icc (0 : Fin 4 → ℝ) (fun _ => c) ⊆ quarticRegion d := by
    intro t ht
    constructor
    · exact ht.1
    · have hquartic (i : Fin 4) : (t i) ^ 4 ≤ c := by
        have hpow : (t i) ^ 4 ≤ c ^ 4 :=
          pow_le_pow_left₀ (ht.1 i) (ht.2 i) 4
        have hsmall : c ^ 4 ≤ c := by
          simpa using Real.rpow_le_self_of_le_one hc_pos.le hc_le_one
            (by norm_num : (1 : ℝ) ≤ 4)
        exact hpow.trans hsmall
      calc
        (∑ i, (d i : ℝ) * (t i) ^ 4) ≤ ∑ i, (d i : ℝ) * c := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hquartic i) (Nat.cast_nonneg _)
        _ = (S : ℝ) * c := by simp [S, Finset.sum_mul]
        _ ≤ 1 := by
          dsimp [c]
          rw [show (S : ℝ) * (1 / ((S : ℝ) + 1)) =
            (S : ℝ) / ((S : ℝ) + 1) by ring]
          exact (div_le_iff₀ (by positivity : (0 : ℝ) < (S : ℝ) + 1)).mpr (by linarith)
  have hfinite : MeasureTheory.volume (quarticRegion d) ≠ ⊤ :=
    (quarticRegion_isBounded d hd).measure_lt_top.ne
  have hboxvol : MeasureTheory.volume.real
      (Set.Icc (0 : Fin 4 → ℝ) (fun _ => c)) = c ^ 4 := by
    change (MeasureTheory.volume (Set.Icc (0 : Fin 4 → ℝ) (fun _ => c))).toReal = c ^ 4
    rw [Real.volume_Icc_pi_toReal]
    · simp
    · exact fun _ => hc_pos.le
  unfold fixedPartVolume
  exact (by rw [hboxvol]; positivity :
    0 < MeasureTheory.volume.real (Set.Icc (0 : Fin 4 → ℝ) (fun _ => c))).trans_le
      (MeasureTheory.measureReal_mono hbox hfinite)

theorem fixedPartVolume_le_one (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    fixedPartVolume d ≤ 1 := by
  unfold fixedPartVolume
  calc
    MeasureTheory.volume.real (quarticRegion d)
        ≤ MeasureTheory.volume.real (Set.Icc (0 : Fin 4 → ℝ) 1) :=
          MeasureTheory.measureReal_mono (quarticRegion_subset_unitBox d hd)
            (by simp [Real.volume_Icc_pi])
    _ = 1 := by
      change (MeasureTheory.volume (Set.Icc (0 : Fin 4 → ℝ) 1)).toReal = 1
      rw [Real.volume_Icc_pi_toReal]
      · simp
      · exact fun _ => zero_le_one

/-- A coefficient-uniform bound on the leading volume. The box containing the
quartic region has side length `dᵢ ^ (-1/4)` in coordinate `i`. -/
theorem fixedPartVolume_le_coeff_product (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    fixedPartVolume d ≤ ∏ i, (d i : ℝ) ^ (-(4 : ℝ)⁻¹) := by
  let b : Fin 4 → ℝ := fun i => (d i : ℝ) ^ (-(4 : ℝ)⁻¹)
  have hb_pos (i : Fin 4) : 0 < b i := by
    dsimp [b]
    have : 0 < (d i : ℝ) := by exact_mod_cast hd i
    positivity
  have hb_quartic (i : Fin 4) : b i ^ 4 = (d i : ℝ)⁻¹ := by
    dsimp [b]
    rw [Real.rpow_neg (Nat.cast_nonneg _), inv_pow]
    simpa using
      congrArg Inv.inv (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (d i))
        (by decide : (4 : ℕ) ≠ 0))
  have hbox : quarticRegion d ⊆ Set.Icc (0 : Fin 4 → ℝ) b := by
    intro t ht
    constructor
    · exact ht.1
    · intro i
      have hnonneg (j : Fin 4) : 0 ≤ (d j : ℝ) * (t j) ^ 4 :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ht.1 j) _)
      have hterm : (d i : ℝ) * (t i) ^ 4 ≤ (1 : ℝ) :=
        (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)).trans ht.2
      have hcoef : 0 < (d i : ℝ) := by exact_mod_cast hd i
      have hquartic : (t i) ^ 4 ≤ (b i) ^ 4 := by
        rw [hb_quartic]
        rw [← one_div]
        exact (le_div_iff₀ hcoef).2 (by nlinarith [hterm])
      exact le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (hb_pos i).le hquartic
  unfold fixedPartVolume
  calc
    MeasureTheory.volume.real (quarticRegion d)
        ≤ MeasureTheory.volume.real (Set.Icc (0 : Fin 4 → ℝ) b) :=
          MeasureTheory.measureReal_mono hbox
            ((Metric.isBounded_Icc (0 : Fin 4 → ℝ) b).measure_lt_top.ne)
    _ = ∏ i, (d i : ℝ) ^ (-(4 : ℝ)⁻¹) := by
      change (MeasureTheory.volume (Set.Icc (0 : Fin 4 → ℝ) b)).toReal = _
      rw [Real.volume_Icc_pi_toReal]
      · simp [b]
      · exact fun i => (hb_pos i).le

/-- The ordinary integer grid has the expected density in the quartic region.
This is the unshifted lattice limit used in the residue-class argument. -/
theorem quarticRegion_lattice_limit (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card ↑(quarticRegion d ∩
          (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))) : ℝ) /
          (n : ℝ) ^ 4)
      Filter.atTop (nhds (fixedPartVolume d)) := by
  simpa [fixedPartVolume] using
    (tendsto_card_div_pow_atTop_volume (s := quarticRegion d)
      (quarticRegion_isBounded d hd) (quarticRegion_measurableSet d)
      (quarticRegion_frontier_null d))

/-- A nonnegative integer vector, scaled by `n`, is in the standard lattice. -/
private theorem gridPoint_mem_lattice (n : ℕ) [NeZero n] (k : Fin 4 → ℕ) :
    (fun i => (k i : ℝ) / n) ∈
      (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4))) := by
  apply (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).2
  intro i
  refine ⟨(k i : ℤ), ?_⟩
  simp [mul_div_cancel₀, NeZero.ne n]

/-- Conversely, a lattice point in the nonnegative orthant has nonnegative
integer coordinates after scaling. -/
private theorem exists_nat_of_gridPoint (n : ℕ) [NeZero n]
    (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hgrid : v ∈ (n : ℝ)⁻¹ •
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))) :
    ∃ k : Fin 4 → ℕ, (fun i => (k i : ℝ) / n) = v := by
  have h := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).1 hgrid
  choose z hz using h
  have hz' (i : Fin 4) : (z i : ℝ) = (n : ℝ) * v i := by
    simpa using hz i
  have hz_nonneg (i : Fin 4) : 0 ≤ z i := by
    have hreal : 0 ≤ (z i : ℝ) := by
      rw [hz' i]
      exact mul_nonneg (Nat.cast_nonneg _) (hv i)
    exact_mod_cast hreal
  refine ⟨fun i => (z i).toNat, funext fun i => ?_⟩
  have hzi : ((z i).toNat : ℝ) = (z i : ℝ) := by
    exact_mod_cast (Int.natCast_toNat_eq_self.mpr (hz_nonneg i))
  rw [hzi, hz' i]
  exact mul_div_cancel_left₀ (v i) (Nat.cast_ne_zero.mpr (NeZero.ne n))

private theorem gridPoint_mem_quarticRegion_iff (d : Fin 4 → ℕ) (n : ℕ) [NeZero n]
    (k : Fin 4 → ℕ) :
    (fun i => (k i : ℝ) / n) ∈ quarticRegion d ↔ quarticForm d k ≤ n ^ 4 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsum :
      (∑ i, (d i : ℝ) * ((k i : ℝ) / n) ^ 4) =
        (quarticForm d k : ℝ) / (n : ℝ) ^ 4 := by
    calc
      _ = ∑ i, ((d i : ℝ) * (k i : ℝ) ^ 4) / (n : ℝ) ^ 4 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_pow]
        ring
      _ = (quarticForm d k : ℝ) / (n : ℝ) ^ 4 := by
        rw [← Finset.sum_div]
        simp [quarticForm]
  rw [quarticRegion, Set.mem_ofPred_eq, hsum]
  have hnonneg : ∀ i, (0 : ℝ) ≤ (k i : ℝ) / n :=
    fun i => div_nonneg (Nat.cast_nonneg _) hn.le
  constructor
  · intro h
    have hh := h.2
    rw [div_le_iff₀ (pow_pos hn 4), one_mul] at hh
    exact_mod_cast hh
  · intro h
    refine ⟨hnonneg, ?_⟩
    rw [div_le_iff₀ (pow_pos hn 4), one_mul]
    exact_mod_cast h

/-- The standard lattice count is exactly the count of nonnegative natural
quadruples whose quartic form is at most `n⁴`. -/
private theorem natGridCount_eq_latticeCount (d : Fin 4 → ℕ) (n : ℕ) [NeZero n] :
    Nat.card {k : Fin 4 → ℕ // quarticForm d k ≤ n ^ 4} =
      Nat.card ↑(quarticRegion d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))) := by
  let f : {k : Fin 4 → ℕ // quarticForm d k ≤ n ^ 4} →
      ↑(quarticRegion d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))) :=
    fun k => ⟨fun i => (k.val i : ℝ) / n,
      ⟨(gridPoint_mem_quarticRegion_iff d n k.val).2 k.property,
        gridPoint_mem_lattice n k.val⟩⟩
  have hf_inj : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun v : Fin 4 → ℝ => v i) (congrArg Subtype.val h)
    change (k.val i : ℝ) / n = (l.val i : ℝ) / n at hi
    exact_mod_cast (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne n))).1 hi
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨k, hk⟩ := exists_nat_of_gridPoint n v.val v.property.1.1 v.property.2
    have hform : quarticForm d k ≤ n ^ 4 :=
      (gridPoint_mem_quarticRegion_iff d n k).1 (hk.symm ▸ v.property.1)
    refine ⟨⟨k, hform⟩, ?_⟩
    apply Subtype.ext
    exact hk
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)

private theorem natGridCount_limit (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {k : Fin 4 → ℕ // quarticForm d k ≤ n ^ 4} : ℝ) / (n : ℝ) ^ 4)
      Filter.atTop (nhds (fixedPartVolume d)) := by
  refine (quarticRegion_lattice_limit d hd).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact congrArg (fun c : ℕ => (c : ℝ) / (n : ℝ) ^ 4)
    (natGridCount_eq_latticeCount d n).symm

/-- The same quartic region with all four coordinates strictly positive. -/
private def quarticRegionPos (d : Fin 4 → ℕ) : Set (Fin 4 → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ (∑ i, (d i : ℝ) * (t i) ^ 4) ≤ 1}

private theorem quarticRegionPos_eq (d : Fin 4 → ℕ) :
    quarticRegionPos d = quarticRegion d ∩
      Set.univ.pi (fun _ : Fin 4 => Set.Ioi (0 : ℝ)) := by
  ext t
  constructor
  · intro ht
    exact ⟨⟨fun i => (ht.1 i).le, ht.2⟩, by simpa [Set.mem_pi] using ht.1⟩
  · rintro ⟨ht, hp⟩
    exact ⟨by simpa [Set.mem_pi] using hp, ht.2⟩

private theorem quarticRegionPos_bounded (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    Bornology.IsBounded (quarticRegionPos d) := by
  apply (quarticRegion_isBounded d hd).subset
  intro t ht
  exact ⟨fun i => (ht.1 i).le, ht.2⟩

private theorem quarticRegionPos_measurable (d : Fin 4 → ℕ) :
    MeasurableSet (quarticRegionPos d) := by
  rw [quarticRegionPos_eq]
  exact (quarticRegion_measurableSet d).inter
    ((isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)).measurableSet)

private theorem quarticRegionPos_convex (d : Fin 4 → ℕ) :
    Convex ℝ (quarticRegionPos d) := by
  rw [quarticRegionPos_eq]
  exact (quarticRegion_convex d).inter
    (convex_pi (fun _ _ => convex_Ioi (0 : ℝ)))

private theorem quarticRegionPos_frontier_null (d : Fin 4 → ℕ) :
    MeasureTheory.volume (frontier (quarticRegionPos d)) = 0 :=
  Convex.addHaar_frontier MeasureTheory.volume (quarticRegionPos_convex d)

private theorem quarticRegionPos_volume_eq (d : Fin 4 → ℕ) :
    MeasureTheory.volume (quarticRegionPos d) = MeasureTheory.volume (quarticRegion d) := by
  have hsub : quarticRegionPos d ⊆ quarticRegion d := by
    intro t ht
    exact ⟨fun i => (ht.1 i).le, ht.2⟩
  have hdiff : quarticRegion d \ quarticRegionPos d ⊆
      ⋃ i : Fin 4, {t : Fin 4 → ℝ | t i = 0} := by
    intro t ht
    have hnot : ¬∀ i, 0 < t i := by
      intro hp
      exact ht.2 ⟨hp, ht.1.2⟩
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact le_antisymm (le_of_not_gt hi) (ht.1.1 i)
  have hzero : MeasureTheory.volume
      (⋃ i : Fin 4, {t : Fin 4 → ℝ | t i = 0}) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro i
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 4 => MeasureTheory.volume) i 0
  exact MeasureTheory.measure_eq_measure_of_null_sdiff hsub
    (MeasureTheory.measure_mono_null hdiff hzero)

private theorem gridPoint_mem_quarticRegionPos_iff (d : Fin 4 → ℕ)
    (n : ℕ) [NeZero n] (k : Fin 4 → ℕ) :
    (fun i => (k i : ℝ) / n) ∈ quarticRegionPos d ↔
      (∀ i, 0 < k i) ∧ quarticForm d k ≤ n ^ 4 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  rw [quarticRegionPos_eq, Set.mem_inter_iff, gridPoint_mem_quarticRegion_iff]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioi]
  constructor
  · rintro ⟨hform, hp⟩
    exact ⟨fun i => by
      have hi : (0 : ℝ) < (k i : ℝ) := by
        simpa using (lt_div_iff₀ hn).1 (hp i)
      exact_mod_cast hi, hform⟩
  · rintro ⟨hp, hform⟩
    exact ⟨hform, fun i => div_pos (by exact_mod_cast hp i) hn⟩

private theorem natGridPosCount_eq_latticeCount (d : Fin 4 → ℕ)
    (n : ℕ) [NeZero n] :
    Nat.card {k : Fin 4 → ℕ // (∀ i, 0 < k i) ∧ quarticForm d k ≤ n ^ 4} =
      Nat.card ↑(quarticRegionPos d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))) := by
  let f : {k : Fin 4 → ℕ // (∀ i, 0 < k i) ∧ quarticForm d k ≤ n ^ 4} →
      ↑(quarticRegionPos d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 4)))) :=
    fun k => ⟨fun i => (k.val i : ℝ) / n,
      ⟨(gridPoint_mem_quarticRegionPos_iff d n k.val).2 k.property,
        gridPoint_mem_lattice n k.val⟩⟩
  have hf_inj : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun v : Fin 4 → ℝ => v i) (congrArg Subtype.val h)
    change (k.val i : ℝ) / n = (l.val i : ℝ) / n at hi
    exact_mod_cast (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne n))).1 hi
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨k, hk⟩ := exists_nat_of_gridPoint n v.val
      (fun i => (v.property.1.1 i).le) v.property.2
    have hform : (∀ i, 0 < k i) ∧ quarticForm d k ≤ n ^ 4 :=
      (gridPoint_mem_quarticRegionPos_iff d n k).1 (hk.symm ▸ v.property.1)
    refine ⟨⟨k, hform⟩, ?_⟩
    apply Subtype.ext
    exact hk
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)

private theorem natGridPosCount_limit (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {k : Fin 4 → ℕ // (∀ i, 0 < k i) ∧ quarticForm d k ≤ n ^ 4} : ℝ) /
          (n : ℝ) ^ 4)
      Filter.atTop (nhds (fixedPartVolume d)) := by
  have h := tendsto_card_div_pow_atTop_volume (s := quarticRegionPos d)
    (quarticRegionPos_bounded d hd) (quarticRegionPos_measurable d)
    (quarticRegionPos_frontier_null d)
  have hv : MeasureTheory.volume.real (quarticRegionPos d) = fixedPartVolume d := by
    simp [fixedPartVolume, MeasureTheory.Measure.real, quarticRegionPos_volume_eq]
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact congrArg (fun c : ℕ => (c : ℝ) / (n : ℝ) ^ 4)
    (natGridPosCount_eq_latticeCount d n).symm

private theorem finite_quarticForm_sublevel (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (X : ℕ) :
    Finite {x : Fin 4 → ℕ // quarticForm d x ≤ X} := by
  let f : {x : Fin 4 → ℕ // quarticForm d x ≤ X} → Fin 4 → Fin (X + 1) :=
    fun x i => ⟨x.val i, Nat.lt_succ_of_le ((quarticForm_coord_le d x.val hd i).trans
      x.property)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

private theorem finite_translatedPositiveResidueCount (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M X : ℕ) [NeZero M]
    (r : Fin 4 → ZMod M) :
    Finite {k : Fin 4 → ℕ //
      quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X} := by
  have := finite_quarticForm_sublevel d hd X
  let f : {k : Fin 4 → ℕ //
      quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X} →
      {x : Fin 4 → ℕ // quarticForm d x ≤ X} :=
    fun k => ⟨fun i => positiveResidueRep M (r i) + M * k.val i, k.property⟩
  apply Finite.of_injective f
  intro k l h
  apply Subtype.ext
  funext i
  have hi := congrFun (congrArg Subtype.val h) i
  exact Nat.mul_left_cancel (NeZero.pos M) (Nat.add_left_cancel hi)

/-- The positive-representative residue grid is squeezed between the
positive and nonnegative ordinary grids at quartic cutoffs. -/
private theorem translatedPositiveResidueCount_bounds (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M n : ℕ) [NeZero M]
    (r : Fin 4 → ZMod M) :
    Nat.card {j : Fin 4 → ℕ // (∀ i, 0 < j i) ∧ quarticForm d j ≤ n ^ 4} ≤
      translatedPositiveResidueCount d M ((M * n) ^ 4) r ∧
    translatedPositiveResidueCount d M ((M * n) ^ 4) r ≤
      Nat.card {j : Fin 4 → ℕ // quarticForm d j ≤ n ^ 4} := by
  classical
  have := finite_translatedPositiveResidueCount d hd M ((M * n) ^ 4) r
  have := finite_quarticForm_sublevel d hd (n ^ 4)
  have hupper : translatedPositiveResidueCount d M ((M * n) ^ 4) r ≤
      Nat.card {j : Fin 4 → ℕ // quarticForm d j ≤ n ^ 4} := by
    let f : {k : Fin 4 → ℕ //
        quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤
          (M * n) ^ 4} →
        {j : Fin 4 → ℕ // quarticForm d j ≤ n ^ 4} :=
      fun k => ⟨k.val, by
        have hc : quarticForm d (fun i => M * k.val i) ≤
            quarticForm d (fun i => positiveResidueRep M (r i) + M * k.val i) :=
          quarticForm_mono d (fun i => Nat.le_add_left _ _)
        rw [quarticForm_nsmul] at hc
        have h := hc.trans k.property
        have h' : M ^ 4 * quarticForm d k.val ≤ M ^ 4 * n ^ 4 := by
          calc
            _ ≤ (M * n) ^ 4 := h
            _ = M ^ 4 * n ^ 4 := mul_pow M n 4
        exact Nat.le_of_mul_le_mul_left h' (pow_pos (NeZero.pos M) 4)⟩
    change Nat.card _ ≤ Nat.card _
    exact Nat.card_le_card_of_injective f (by
      intro k l h
      apply Subtype.ext
      have hh := congrArg (fun z : {j : Fin 4 → ℕ // quarticForm d j ≤ n ^ 4} => z.val) h
      exact hh)
  have hlower :
      Nat.card {j : Fin 4 → ℕ // (∀ i, 0 < j i) ∧ quarticForm d j ≤ n ^ 4} ≤
      translatedPositiveResidueCount d M ((M * n) ^ 4) r := by
    let f : {j : Fin 4 → ℕ // (∀ i, 0 < j i) ∧ quarticForm d j ≤ n ^ 4} →
        {k : Fin 4 → ℕ //
          quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤
            (M * n) ^ 4} :=
      fun j => ⟨fun i => j.val i - 1, by
        have hc : quarticForm d (fun i => positiveResidueRep M (r i) +
              M * (j.val i - 1)) ≤ quarticForm d (fun i => M * j.val i) := by
          apply quarticForm_mono d
          intro i
          change positiveResidueRep M (r i) + M * (j.val i - 1) ≤ M * j.val i
          have hj : j.val i = (j.val i - 1) + 1 :=
            (Nat.sub_add_cancel (j.property.1 i)).symm
          rw [hj]
          calc
            positiveResidueRep M (r i) + M * (j.val i - 1)
                ≤ M + M * (j.val i - 1) :=
                  Nat.add_le_add_right (positiveResidueRep_le M (r i)) _
            _ = M * ((j.val i - 1) + 1) := by ring
        rw [quarticForm_nsmul] at hc
        calc
          _ ≤ M ^ 4 * quarticForm d j.val := hc
          _ ≤ M ^ 4 * n ^ 4 := Nat.mul_le_mul_left _ j.property.2
          _ = (M * n) ^ 4 := by ring⟩
    change Nat.card _ ≤ Nat.card _
    exact Nat.card_le_card_of_injective f (by
      intro j l h
      apply Subtype.ext
      funext i
      have hi := congrFun (congrArg (fun z : {k : Fin 4 → ℕ //
        quarticForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤
          (M * n) ^ 4} => z.val) h) i
      have hj : j.val i = (j.val i - 1) + 1 :=
        (Nat.sub_add_cancel (j.property.1 i)).symm
      have hl : l.val i = (l.val i - 1) + 1 :=
        (Nat.sub_add_cancel (l.property.1 i)).symm
      change j.val i - 1 = l.val i - 1 at hi
      omega)
  exact ⟨hlower, hupper⟩

/-- Along quartic cutoffs, the fixed-residue count has the expected density. -/
private theorem residueVector_quartic_asymptotic (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M : ℕ) [NeZero M]
    (r : Fin 4 → ZMod M) :
    Filter.Tendsto
      (fun n : ℕ =>
        (residueVectorCount d M ((M * n) ^ 4) r : ℝ) / ((M * n : ℕ) : ℝ) ^ 4)
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 4)) := by
  have hpos : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {j : Fin 4 → ℕ // (∀ i, 0 < j i) ∧ quarticForm d j ≤ n ^ 4} : ℝ) /
          ((M * n : ℕ) : ℝ) ^ 4)
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 4)) := by
    convert (natGridPosCount_limit d hd).div_const ((M : ℝ) ^ 4) using 1
    funext n
    simp only [Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  have hnon : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {j : Fin 4 → ℕ // quarticForm d j ≤ n ^ 4} : ℝ) /
          ((M * n : ℕ) : ℝ) ^ 4)
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 4)) := by
    convert (natGridCount_limit d hd).div_const ((M : ℝ) ^ 4) using 1
    funext n
    simp only [Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  refine Filter.Tendsto.squeeze' hpos hnon ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : (0 : ℝ) < ((M * n : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos M) hn) 4
    have hbound := (translatedPositiveResidueCount_bounds d hd M n r).1
    have hcount : residueVectorCount d M ((M * n) ^ 4) r =
        translatedPositiveResidueCount d M ((M * n) ^ 4) r :=
      (residueVectorCount_eq_residueNatCount d hd M _ r).trans
        (residueNatCount_eq_translatedPositiveResidueCount d M _ r)
    rw [hcount]
    exact (div_le_div_iff_of_pos_right hden).2 (by exact_mod_cast hbound)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hden : (0 : ℝ) < ((M * n : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos M) hn) 4
    have hbound := (translatedPositiveResidueCount_bounds d hd M n r).2
    have hcount : residueVectorCount d M ((M * n) ^ 4) r =
        translatedPositiveResidueCount d M ((M * n) ^ 4) r :=
      (residueVectorCount_eq_residueNatCount d hd M _ r).trans
        (residueNatCount_eq_translatedPositiveResidueCount d M _ r)
    rw [hcount]
    exact (div_le_div_iff_of_pos_right hden).2 (by exact_mod_cast hbound)

private def quarticCutoffIndex (M X : ℕ) : ℕ := Nat.nthRoot 4 X / M

private theorem quarticCutoffIndex_bracket (M X : ℕ) [NeZero M] :
    (M * quarticCutoffIndex M X) ^ 4 ≤ X ∧
      X < (M * (quarticCutoffIndex M X + 1)) ^ 4 := by
  let q := Nat.nthRoot 4 X
  have hleft : M * (q / M) ≤ q := by
    simpa [mul_comm] using Nat.div_mul_le_self q M
  have hright : q < M * (q / M + 1) := by
    simpa [mul_comm] using
      (Nat.div_lt_iff_lt_mul (NeZero.pos M)).1 (Nat.lt_succ_self (q / M))
  change (M * (q / M)) ^ 4 ≤ X ∧ X < (M * (q / M + 1)) ^ 4
  constructor
  · exact (pow_le_pow_left₀ (Nat.zero_le _) hleft 4).trans
      (Nat.pow_nthRoot_le (.inl (by decide : (4 : ℕ) ≠ 0)))
  · exact (Nat.lt_pow_nthRoot_add_one (by decide : (4 : ℕ) ≠ 0) X).trans_le
      (pow_le_pow_left₀ (Nat.zero_le _)
        (Nat.succ_le_iff.mpr hright) 4)

private theorem quarticCutoffIndex_tendsto (M : ℕ) [NeZero M] :
    Filter.Tendsto (quarticCutoffIndex M) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop ((M * b) ^ 4)] with X hX
  have hroot : M * b ≤ Nat.nthRoot 4 X :=
    (Nat.le_nthRoot_iff (by decide : (4 : ℕ) ≠ 0)).2 hX
  exact (Nat.le_div_iff_mul_le (NeZero.pos M)).2 (by
    simpa [quarticCutoffIndex, mul_comm] using hroot)

private theorem quarticCutoff_ratio_tendsto (M : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun n : ℕ => (((M * n : ℕ) : ℝ) ^ 4) /
        (((M * (n + 1) : ℕ) : ℝ) ^ 4))
      Filter.atTop (nhds (1 : ℝ)) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).pow 4
  simpa only [one_pow] using h.congr' (by
    filter_upwards [] with n
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_pow]
    field_simp)

private theorem quarticCutoff_inv_ratio_tendsto (M : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun n : ℕ => (((M * (n + 1) : ℕ) : ℝ) ^ 4) /
        (((M * n : ℕ) : ℝ) ^ 4))
      Filter.atTop (nhds (1 : ℝ)) := by
  have h := (quarticCutoff_ratio_tendsto M).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_one] using h.congr' (by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    simp only [inv_div])

/-- The fixed-residue count is monotone in its cutoff. -/
theorem residueVectorCount_mono (d : Fin 4 → ℕ) (M : ℕ)
    (r : Fin 4 → ZMod M) : Monotone (fun X => residueVectorCount d M X r) := by
  classical
  intro X Y hXY
  unfold residueVectorCount
  let e : Fin (X + 1) ↪ Fin (Y + 1) :=
    ⟨Fin.castLE (Nat.succ_le_succ hXY),
      Fin.castLE_injective (Nat.succ_le_succ hXY)⟩
  let f : {x : Fin 4 → Fin (X + 1) //
      (∀ i, 0 < (x i).val) ∧
      quarticForm d (fun i => (x i).val) ≤ X ∧
      (∀ i, ((x i).val : ZMod M) = r i)} ↪
      {x : Fin 4 → Fin (Y + 1) //
        (∀ i, 0 < (x i).val) ∧
        quarticForm d (fun i => (x i).val) ≤ Y ∧
        (∀ i, ((x i).val : ZMod M) = r i)} :=
    ⟨fun x => ⟨fun i => e (x.val i), by
      have hv (i : Fin 4) : (e (x.val i)).val = (x.val i).val := rfl
      simp only [hv]
      exact ⟨x.property.1, x.property.2.1.trans hXY, x.property.2.2⟩⟩, by
      intro x y h
      apply Subtype.ext
      funext i
      exact e.injective (congrArg (fun z : Fin 4 → Fin (Y + 1) => z i)
        (congrArg Subtype.val h))⟩
  exact Fintype.card_le_of_injective f f.injective

/-- The lattice-point principle applied to one fixed residue vector. -/
theorem residueVector_asymptotic (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M : ℕ) [NeZero M]
    (r : Fin 4 → ZMod M) :
    Filter.Tendsto
      (fun X : ℕ => (residueVectorCount d M X r : ℝ) / (X : ℝ))
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 4)) := by
  let F : ℕ → ℕ := fun X => residueVectorCount d M X r
  let g : ℕ → ℕ := fun n => (M * n) ^ 4
  let N : ℕ → ℕ := quarticCutoffIndex M
  let C : ℝ := fixedPartVolume d / (M : ℝ) ^ 4
  have hquartic : Filter.Tendsto
      (fun n : ℕ => (F (g n) : ℝ) / (g n : ℝ)) Filter.atTop (nhds C) := by
    simpa [F, g, C] using residueVector_quartic_asymptotic d hd M r
  have hN : Filter.Tendsto N Filter.atTop Filter.atTop := quarticCutoffIndex_tendsto M
  have hNsucc : Filter.Tendsto (fun X => N X + 1) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp hN
  have hlow : Filter.Tendsto
      (fun X : ℕ => (F (g (N X)) : ℝ) / (g (N X + 1) : ℝ))
      Filter.atTop (nhds C) := by
    have hprod := (hquartic.comp hN).mul ((quarticCutoff_ratio_tendsto M).comp hN)
    have hprod' : Filter.Tendsto
        (fun X : ℕ => ((F (g (N X)) : ℝ) / (g (N X) : ℝ)) *
          ((g (N X) : ℝ) / (g (N X + 1) : ℝ)))
        Filter.atTop (nhds C) := by
      simpa [g, C] using hprod
    refine hprod'.congr' ?_
    filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hgn : (g (N X) : ℝ) ≠ 0 := by
      have h : 0 < g (N X) := pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 4
      exact_mod_cast h.ne'
    have hgn1 : (g (N X + 1) : ℝ) ≠ 0 := by
      have h : 0 < g (N X + 1) :=
        pow_pos (Nat.mul_pos (NeZero.pos M) (Nat.succ_pos _)) 4
      exact_mod_cast h.ne'
    field_simp
  have hupp : Filter.Tendsto
      (fun X : ℕ => (F (g (N X + 1)) : ℝ) / (g (N X) : ℝ))
      Filter.atTop (nhds C) := by
    have hprod := (hquartic.comp hNsucc).mul ((quarticCutoff_inv_ratio_tendsto M).comp hN)
    have hprod' : Filter.Tendsto
        (fun X : ℕ => ((F (g (N X + 1)) : ℝ) / (g (N X + 1) : ℝ)) *
          ((g (N X + 1) : ℝ) / (g (N X) : ℝ)))
        Filter.atTop (nhds C) := by
      simpa [g, C] using hprod
    refine hprod'.congr' ?_
    filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hgn : (g (N X) : ℝ) ≠ 0 := by
      have h : 0 < g (N X) := pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 4
      exact_mod_cast h.ne'
    have hgn1 : (g (N X + 1) : ℝ) ≠ 0 := by
      have h : 0 < g (N X + 1) :=
        pow_pos (Nat.mul_pos (NeZero.pos M) (Nat.succ_pos _)) 4
      exact_mod_cast h.ne'
    field_simp
  change Filter.Tendsto (fun X => (F X : ℝ) / (X : ℝ)) Filter.atTop (nhds C)
  refine Filter.Tendsto.squeeze' hlow hupp ?_ ?_
  · filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hbr : g (N X) ≤ X ∧ X < g (N X + 1) :=
      quarticCutoffIndex_bracket M X
    have hX : 0 < X := (pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 4).trans_le hbr.1
    have hg1 : 0 < g (N X + 1) :=
      pow_pos (Nat.mul_pos (NeZero.pos M) (Nat.succ_pos _)) 4
    have hF : F (g (N X)) ≤ F X := residueVectorCount_mono d M r hbr.1
    have hcross : F (g (N X)) * X ≤ F X * g (N X + 1) := by
      calc
        _ ≤ F (g (N X)) * g (N X + 1) := Nat.mul_le_mul_left _ hbr.2.le
        _ ≤ F X * g (N X + 1) := Nat.mul_le_mul_right _ hF
    exact (div_le_div_iff₀ (by exact_mod_cast hg1) (by exact_mod_cast hX)).2
      (by exact_mod_cast hcross)
  · filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hbr : g (N X) ≤ X ∧ X < g (N X + 1) :=
      quarticCutoffIndex_bracket M X
    have hX : 0 < X := (pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 4).trans_le hbr.1
    have hg0 : 0 < g (N X) := pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 4
    have hF : F X ≤ F (g (N X + 1)) := residueVectorCount_mono d M r hbr.2.le
    have hcross : F X * g (N X) ≤ F (g (N X + 1)) * X := by
      calc
        _ ≤ F X * X := Nat.mul_le_mul_left _ hbr.1
        _ ≤ F (g (N X + 1)) * X := Nat.mul_le_mul_right _ hF
    exact (div_le_div_iff₀ (by exact_mod_cast hX) (by exact_mod_cast hg0)).2
      (by exact_mod_cast hcross)

/-- For coprime moduli, the number of admissible residue vectors factors.
The proof should use `ZMod.chineseRemainder` coordinatewise. -/
theorem localCount_mul_of_coprime (d : Fin 4 → ℕ) (m n a : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcoprime : m.Coprime n) :
    localCount d (m * n) a = localCount d m a * localCount d n a := by
  classical
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcoprime
  let E : (Fin 4 → ZMod (m * n)) ≃
      (Fin 4 → ZMod m) × (Fin 4 → ZMod n) :=
    { toFun := fun x => (fun i => (e (x i)).1, fun i => (e (x i)).2)
      invFun := fun yz i => e.symm (yz.1 i, yz.2 i)
      left_inv := by
        intro x
        funext i
        exact e.symm_apply_apply (x i)
      right_inv := by
        intro yz
        apply Prod.ext
        · funext i
          exact congrArg Prod.fst (e.apply_symm_apply (yz.1 i, yz.2 i))
        · funext i
          exact congrArg Prod.snd (e.apply_symm_apply (yz.1 i, yz.2 i)) }
  have he_nat : e (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) := by
    exact map_natCast e a
  have he_form (x : Fin 4 → ZMod (m * n)) :
      e (quarticFormMod (m * n) d x) =
        (quarticFormMod m d (E x).1, quarticFormMod n d (E x).2) := by
    apply Prod.ext
    · simp [quarticFormMod, E, Prod.fst_sum]
    · simp [quarticFormMod, E, Prod.snd_sum]
  have hp (x : Fin 4 → ZMod (m * n)) :
      quarticFormMod (m * n) d x = (a : ZMod (m * n)) ↔
        quarticFormMod m d (E x).1 = (a : ZMod m) ∧
          quarticFormMod n d (E x).2 = (a : ZMod n) := by
    constructor
    · intro hx
      have hh := congrArg e hx
      rw [he_form x, he_nat] at hh
      exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
    · rintro ⟨hm, hn⟩
      apply e.injective
      rw [he_form x, he_nat]
      exact Prod.ext hm hn
  let Esub :
      {x : Fin 4 → ZMod (m * n) // quarticFormMod (m * n) d x = (a : ZMod (m * n))} ≃
      {yz : (Fin 4 → ZMod m) × (Fin 4 → ZMod n) //
        quarticFormMod m d yz.1 = (a : ZMod m) ∧
          quarticFormMod n d yz.2 = (a : ZMod n)} :=
    E.subtypeEquiv hp
  let Eprod :
      {x : Fin 4 → ZMod (m * n) // quarticFormMod (m * n) d x = (a : ZMod (m * n))} ≃
        {x : Fin 4 → ZMod m // quarticFormMod m d x = (a : ZMod m)} ×
        {x : Fin 4 → ZMod n // quarticFormMod n d x = (a : ZMod n)} :=
    Esub.trans (Equiv.subtypeProdEquivProd
      (p := fun x : Fin 4 → ZMod m => quarticFormMod m d x = (a : ZMod m))
      (q := fun x : Fin 4 → ZMod n => quarticFormMod n d x = (a : ZMod n)))
  exact (Fintype.card_congr Eprod).trans (by simp [localCount])

/-- The bounded count is the sum of its residue-vector fibers. -/
theorem fixedPartCount_eq_sum_residueVectorCount (d : Fin 4 → ℕ)
    (M a X : ℕ) [NeZero M] :
    fixedPartCount d M a X =
      ∑ r ∈ (Finset.univ.filter fun r : Fin 4 → ZMod M =>
        quarticFormMod M d r = (a : ZMod M)), residueVectorCount d M X r := by
  classical
  let B : Finset (Fin 4 → Fin (X + 1)) :=
    Finset.univ.filter fun x =>
      (∀ i, 0 < (x i).val) ∧ quarticForm d (fun i => (x i).val) ≤ X
  let T : Finset (Fin 4 → ZMod M) :=
    Finset.univ.filter fun r => quarticFormMod M d r = (a : ZMod M)
  let R : (Fin 4 → Fin (X + 1)) → (Fin 4 → ZMod M) :=
    fun x i => ((x i).val : ZMod M)
  have hfull : (B.filter fun x => R x ∈ T).card = fixedPartCount d M a X := by
    simp [B, T, R, fixedPartCount, Fintype.card_subtype,
      Finset.filter_filter, quarticForm_cast, and_assoc]
  have hfiber (r : Fin 4 → ZMod M) :
      (B.filter fun x => R x = r).card = residueVectorCount d M X r := by
    simp [B, R, residueVectorCount, Fintype.card_subtype,
      Finset.filter_filter, funext_iff, and_assoc]
  calc
    fixedPartCount d M a X = (B.filter fun x => R x ∈ T).card := hfull.symm
    _ = ∑ r ∈ T, (B.filter fun x => R x = r).card :=
      (Finset.sum_card_fiberwise_eq_card_filter B T R).symm
    _ = ∑ r ∈ T, residueVectorCount d M X r := by
      apply Finset.sum_congr rfl
      intro r _
      exact hfiber r
    _ = _ := rfl

/-- The fixed-coefficient count in the quartic complement argument, with the
leading constant expressed as the region volume. It follows by summing the
residue-vector limits over the finitely many admissible vectors. -/
theorem fixedPartCount_asymptotic (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M a : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun X : ℕ => (fixedPartCount d M a X : ℝ) / (X : ℝ))
      Filter.atTop
      (nhds (fixedPartVolume d * (localCount d M a : ℝ) / (M : ℝ) ^ 4)) := by
  classical
  let T : Finset (Fin 4 → ZMod M) :=
    Finset.univ.filter fun r => quarticFormMod M d r = (a : ZMod M)
  have hsum :
      Filter.Tendsto
        (fun X : ℕ => ∑ r ∈ T, (residueVectorCount d M X r : ℝ) / (X : ℝ))
        Filter.atTop
        (nhds (∑ r ∈ T, fixedPartVolume d / (M : ℝ) ^ 4)) :=
    tendsto_finsetSum T (fun r _ => residueVector_asymptotic d hd M r)
  have hfun :
      (fun X : ℕ => (fixedPartCount d M a X : ℝ) / (X : ℝ)) =
        (fun X : ℕ => ∑ r ∈ T, (residueVectorCount d M X r : ℝ) / (X : ℝ)) := by
    funext X
    rw [fixedPartCount_eq_sum_residueVectorCount]
    change ((∑ r ∈ T, residueVectorCount d M X r : ℕ) : ℝ) / (X : ℝ) = _
    simp only [Nat.cast_sum, Finset.sum_div]
  have hcard : T.card = localCount d M a := by
    simp [T, localCount, Fintype.card_subtype]
  have hlimit :
      (∑ r ∈ T, fixedPartVolume d / (M : ℝ) ^ 4) =
        fixedPartVolume d * (localCount d M a : ℝ) / (M : ℝ) ^ 4 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
    ring
  rw [← hfun, hlimit] at hsum
  exact hsum

/-- The number of allowed positive roots in one coordinate. -/
private noncomputable def quarticRootLimit (d X : ℕ) : ℕ :=
  Nat.floor (((X : ℝ) / (d : ℝ)) ^ (1 / 4 : ℝ))

private theorem quarticRoot_le_limit {d X x : ℕ}
    (hd : 0 < d) (hx : 0 < x) (hterm : d * x ^ 4 ≤ X) :
    x ≤ quarticRootLimit d X := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hquot : (x : ℝ) ^ 4 ≤ (X : ℝ) / (d : ℝ) := by
    apply (le_div_iff₀ hdreal).2
    simpa only [mul_comm] using (show (d : ℝ) * (x : ℝ) ^ 4 ≤ X by
      exact_mod_cast hterm)
  have hroot :
      (x : ℝ) ≤ ((X : ℝ) / (d : ℝ)) ^ (1 / 4 : ℝ) := by
    have hpow := Real.rpow_le_rpow
      (by positivity : 0 ≤ (x : ℝ) ^ 4) hquot
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hsimp : ((x : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (x : ℝ) := by
      convert Real.pow_rpow_inv_natCast
        (by positivity : 0 ≤ (x : ℝ))
        (by norm_num : (4 : ℕ) ≠ 0) using 1; norm_num
    exact hsimp ▸ hpow
  have hy : 0 ≤ ((X : ℝ) / (d : ℝ)) ^ (1 / 4 : ℝ) := by positivity
  exact (Nat.le_floor_iff hy).2 hroot

/-- The elementary box bound used to dominate the coefficient sum. It is
uniform in the modulus and residue class. -/
theorem fixedPartCount_le_weight (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (M a X : ℕ) :
    (fixedPartCount d M a X : ℝ) ≤
      (X : ℝ) * ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ)) := by
  classical
  let B : Type := {x : Fin 4 → Fin (X + 1) //
    (∀ i, 0 < (x i).val) ∧
    quarticForm d (fun i => (x i).val) ≤ X ∧
    (quarticForm d (fun i => (x i).val) : ZMod M) = (a : ZMod M)}
  let e : B → ((i : Fin 4) → Fin (quarticRootLimit (d i) X)) :=
    fun x i => ⟨(x.val i).val - 1, by
      have hterm : d i * (x.val i).val ^ 4 ≤ X :=
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun j : Fin 4 => d j * (x.val j).val ^ 4)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans x.property.2.1
      have hlim := quarticRoot_le_limit (hd i) (x.property.1 i) hterm
      exact (Nat.sub_lt (x.property.1 i) (by decide)).trans_le hlim⟩
  have he : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    funext i
    have hi := congrArg Fin.val (congrFun h i)
    change (x.val i).val - 1 = (y.val i).val - 1 at hi
    apply Fin.ext
    have hx := x.property.1 i
    have hy := y.property.1 i
    omega
  have hcard : fixedPartCount d M a X ≤
      ∏ i : Fin 4, quarticRootLimit (d i) X := by
    change Fintype.card B ≤ _
    simpa using Fintype.card_le_of_injective e he
  have hcast : (fixedPartCount d M a X : ℝ) ≤
      ∏ i : Fin 4, (quarticRootLimit (d i) X : ℝ) := by
    exact_mod_cast hcard
  have hfloor (i : Fin 4) :
      (quarticRootLimit (d i) X : ℝ) ≤
        ((X : ℝ) / (d i : ℝ)) ^ (1 / 4 : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hfactor (i : Fin 4) :
      ((X : ℝ) / (d i : ℝ)) ^ (1 / 4 : ℝ) =
        (X : ℝ) ^ (1 / 4 : ℝ) * (d i : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.div_rpow (Nat.cast_nonneg X) (Nat.cast_nonneg _),
      Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have hX4 : ((X : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (X : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X) (1 / 4 : ℝ) 4]
    norm_num
  calc
    (fixedPartCount d M a X : ℝ)
        ≤ ∏ i : Fin 4, (quarticRootLimit (d i) X : ℝ) := hcast
    _ ≤ ∏ i : Fin 4, ((X : ℝ) / (d i : ℝ)) ^ (1 / 4 : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hfloor i)
    _ = (X : ℝ) * ∏ i, (d i : ℝ) ^ (-(1 / 4 : ℝ)) := by
      simp_rw [hfactor]
      simp only [Fin.prod_univ_four]
      conv_rhs => lhs; rw [← hX4]
      ring

/-- The product of the four canonical coefficient weights. -/
noncomputable def coefficientWeight (d : Fin 4 → CanonicalParts) : ℝ :=
  ∏ i, ((d i).val : ℝ) ^ (-(1 / 4 : ℝ))

theorem coefficientWeight_nonneg (d : Fin 4 → CanonicalParts) :
    0 ≤ coefficientWeight d := by
  unfold coefficientWeight
  positivity

theorem summable_coefficientWeight : Summable coefficientWeight := by
  let w : CanonicalParts → ℝ := fun d => (d.val : ℝ) ^ (-(1 / 4 : ℝ))
  have hw : Summable w := summable_canonicalPart_weight
  have hw0 : ∀ d, 0 ≤ w d := fun _ => by dsimp [w]; positivity
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
      w t.1 * w t.2) :=
    hw.mul_of_nonneg hw hw0 hw0
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
    change w (d 0) * (w (d 1) * (w (d 2) * w (d 3))) = coefficientWeight d
    simp only [coefficientWeight, Fin.prod_univ_four, w]
    ring)

/-- Dominated convergence for the ordered four-summand first moment. The
summand is normalized before taking the infinite coefficient sum. -/
theorem firstMoment_asymptotic (M a : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun X : ℕ => ∑' d : Fin 4 → CanonicalParts,
        (fixedPartCount (fun i => (d i).val) M a X : ℝ) / (X : ℝ))
      Filter.atTop
      (nhds (∑' d : Fin 4 → CanonicalParts,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4)) := by
  apply tendsto_tsum_of_dominated_convergence summable_coefficientWeight
  · intro d
    exact fixedPartCount_asymptotic (fun i => (d i).val)
      (fun i => (d i).property.pos) M a
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with X hX d
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    have hbound := fixedPartCount_le_weight (fun i => (d i).val)
      (fun i => (d i).property.pos) M a X
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Nat.cast_nonneg _) hXreal.le)]
    apply (div_le_iff₀ hXreal).2
    calc
      (fixedPartCount (fun i => (d i).val) M a X : ℝ)
          ≤ (X : ℝ) * coefficientWeight d := by
            simpa only [coefficientWeight] using hbound
      _ = coefficientWeight d * (X : ℝ) := mul_comm _ _

end Erdos940.Quartic
