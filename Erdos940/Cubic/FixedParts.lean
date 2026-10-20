module

public import Erdos940.Statement
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Counting three cubes with fixed 4-full parts

The definitions here use an ordered triple of positive cube roots. They match
the counting problem in Proposition 4.1 of Beyer de Ryke, *A density deficit
for sums of three cube-full numbers*. The coefficient triple `d` will later
range over canonical 4-full parts.

The region's regularity, ordinary-grid lattice limit, residue-vector limit,
and fixed-parts asymptotic are proved here.
-/

@[expose] public section

namespace Erdos940

open scoped Pointwise

/-- The integer represented by three fixed coefficients and cube roots. -/
def cubeForm (d x : Fin 3 → ℕ) : ℕ :=
  ∑ i, d i * (x i) ^ 3

/-- The same cubic form over `ZMod M`. -/
def cubeFormMod (M : ℕ) (d : Fin 3 → ℕ) (x : Fin 3 → ZMod M) : ZMod M :=
  ∑ i, (d i : ZMod M) * (x i) ^ 3

theorem cubeForm_cast (M : ℕ) (d x : Fin 3 → ℕ) :
    (cubeForm d x : ZMod M) = cubeFormMod M d (fun i => (x i : ZMod M)) := by
  simp [cubeForm, cubeFormMod]

/-- A positive cube root does not exceed the represented integer. -/
theorem cubeForm_coord_le (d x : Fin 3 → ℕ) (hd : ∀ i, 0 < d i)
    (i : Fin 3) : x i ≤ cubeForm d x := by
  by_cases hx : x i = 0
  · simp [hx]
  have hxi : 0 < x i := Nat.pos_of_ne_zero hx
  calc
    x i ≤ (x i) ^ 3 := le_self_pow (Nat.one_le_iff_ne_zero.mpr hxi.ne') (by decide)
    _ ≤ d i * (x i) ^ 3 := le_mul_of_one_le_left (Nat.zero_le _) (hd i)
    _ ≤ cubeForm d x := by
      unfold cubeForm
      exact Finset.single_le_sum (f := fun j : Fin 3 => d j * (x j) ^ 3)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem cubeForm_mono (d : Fin 3 → ℕ) {x y : Fin 3 → ℕ}
    (hxy : x ≤ y) : cubeForm d x ≤ cubeForm d y := by
  unfold cubeForm
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (pow_le_pow_left₀ (Nat.zero_le _) (hxy i) 3)

private theorem cubeForm_nsmul (d x : Fin 3 → ℕ) (M : ℕ) :
    cubeForm d (fun i => M * x i) = M ^ 3 * cubeForm d x := by
  simp only [cubeForm, mul_pow]
  rw [Finset.mul_sum]
  congr 1
  ext i
  ring

/-- Positive ordered triples of cube roots with a bounded sum in one residue
class. The roots are represented by `Fin (X+1)` because every positive root
of a sum at most `X` is itself at most `X` when all coefficients are positive. -/
noncomputable def fixedPartCount (d : Fin 3 → ℕ) (M a X : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : Fin 3 → Fin (X + 1) //
    (∀ i, 0 < (x i).val) ∧
    cubeForm d (fun i => (x i).val) ≤ X ∧
    (cubeForm d (fun i => (x i).val) : ZMod M) = (a : ZMod M)}

/-- The number of admissible residue vectors modulo a positive modulus. -/
noncomputable def localCount (d : Fin 3 → ℕ) (M a : ℕ) [NeZero M] : ℕ := by
  classical
  exact Fintype.card {x : Fin 3 → ZMod M // cubeFormMod M d x = (a : ZMod M)}

/-- Positive lattice points in one fixed vector of residue classes. -/
noncomputable def residueVectorCount (d : Fin 3 → ℕ) (M X : ℕ)
    (r : Fin 3 → ZMod M) : ℕ := by
  classical
  exact Fintype.card {x : Fin 3 → Fin (X + 1) //
    (∀ i, 0 < (x i).val) ∧
    cubeForm d (fun i => (x i).val) ≤ X ∧
    (∀ i, ((x i).val : ZMod M) = r i)}

/-- The same residue-vector count without a cutoff in the coordinate type.
This form is convenient when passing to a translated integer grid. -/
noncomputable def residueNatCount (d : Fin 3 → ℕ) (M X : ℕ)
    (r : Fin 3 → ZMod M) : ℕ :=
  Nat.card {x : Fin 3 → ℕ //
    (∀ i, 0 < x i) ∧ cubeForm d x ≤ X ∧
    (∀ i, (x i : ZMod M) = r i)}

theorem residueVectorCount_eq_residueNatCount (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (M X : ℕ) (r : Fin 3 → ZMod M) :
    residueVectorCount d M X r = residueNatCount d M X r := by
  classical
  let e : {x : Fin 3 → Fin (X + 1) //
      (∀ i, 0 < (x i).val) ∧
      cubeForm d (fun i => (x i).val) ≤ X ∧
      (∀ i, ((x i).val : ZMod M) = r i)} ≃
      {x : Fin 3 → ℕ //
        (∀ i, 0 < x i) ∧ cubeForm d x ≤ X ∧
        (∀ i, (x i : ZMod M) = r i)} :=
    { toFun := fun x => ⟨fun i => (x.val i).val, x.property⟩
      invFun := fun x => ⟨fun i => ⟨x.val i,
          Nat.lt_succ_of_le ((cubeForm_coord_le d x.val hd i).trans
            x.property.2.1)⟩, x.property⟩
      left_inv := by intro x; apply Subtype.ext; funext i; apply Fin.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  unfold residueVectorCount residueNatCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr e

/-- Parameterization of a fixed residue class by its quotient coordinates. -/
noncomputable def translatedResidueCount (d : Fin 3 → ℕ) (M X : ℕ)
    (r : Fin 3 → ZMod M) : ℕ :=
  Nat.card {k : Fin 3 → ℕ //
    (∀ i, 0 < (r i).val + M * k i) ∧
    cubeForm d (fun i => (r i).val + M * k i) ≤ X}

theorem residueNatCount_eq_translatedResidueCount (d : Fin 3 → ℕ)
    (M X : ℕ) [NeZero M] (r : Fin 3 → ZMod M) :
    residueNatCount d M X r = translatedResidueCount d M X r := by
  classical
  let fromK : (Fin 3 → ℕ) → (Fin 3 → ℕ) :=
    fun k i => (r i).val + M * k i
  have hcast (k : Fin 3 → ℕ) (i : Fin 3) :
      (fromK k i : ZMod M) = r i := by
    simp [fromK, ZMod.natCast_val]
  have hrepr (x : Fin 3 → ℕ) (hx : ∀ i, (x i : ZMod M) = r i) (i : Fin 3) :
      fromK (fun i => x i / M) i = x i := by
    have hmod : x i % M = (r i).val := by
      have h := congrArg ZMod.val (hx i)
      simpa [ZMod.val_natCast] using h
    simpa [fromK, ← hmod] using Nat.mod_add_div (x i) M
  let e : {x : Fin 3 → ℕ //
      (∀ i, 0 < x i) ∧ cubeForm d x ≤ X ∧
      (∀ i, (x i : ZMod M) = r i)} ≃
      {k : Fin 3 → ℕ //
        (∀ i, 0 < (r i).val + M * k i) ∧
        cubeForm d (fun i => (r i).val + M * k i) ≤ X} :=
    { toFun := fun x => ⟨fun i => x.val i / M, by
        have heq : fromK (fun i => x.val i / M) = x.val :=
          funext (hrepr x.val x.property.2.2)
        change (∀ i, 0 < fromK (fun i => x.val i / M) i) ∧
          cubeForm d (fromK (fun i => x.val i / M)) ≤ X
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
def positiveResidueRep (M : ℕ) [NeZero M] (r : ZMod M) : ℕ :=
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

/-- Positive representatives make every shifted quotient triple positive,
including the zero residue class. -/
noncomputable def translatedPositiveResidueCount (d : Fin 3 → ℕ) (M X : ℕ)
    [NeZero M] (r : Fin 3 → ZMod M) : ℕ :=
  Nat.card {k : Fin 3 → ℕ //
    cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X}

theorem residueNatCount_eq_translatedPositiveResidueCount (d : Fin 3 → ℕ)
    (M X : ℕ) [NeZero M] (r : Fin 3 → ZMod M) :
    residueNatCount d M X r = translatedPositiveResidueCount d M X r := by
  classical
  let rep : Fin 3 → ℕ := fun i => positiveResidueRep M (r i)
  let fromK : (Fin 3 → ℕ) → (Fin 3 → ℕ) := fun k i => rep i + M * k i
  have hcast (k : Fin 3 → ℕ) (i : Fin 3) : (fromK k i : ZMod M) = r i := by
    simp [fromK, rep, positiveResidueRep_cast]
  have hpos (k : Fin 3 → ℕ) (i : Fin 3) : 0 < fromK k i := by
    exact (positiveResidueRep_pos M (r i)).trans_le (Nat.le_add_right _ _)
  have hrepr (x : Fin 3 → ℕ) (hx : ∀ i, 0 < x i)
      (hr : ∀ i, (x i : ZMod M) = r i) :
      ∃ k : Fin 3 → ℕ, fromK k = x := by
    choose k hk using fun i => exists_positiveResidueRep M (r i) (x i) (hx i) (hr i)
    exact ⟨k, funext fun i => (hk i).symm⟩
  choose toK htoK using fun x : {x : Fin 3 → ℕ //
      (∀ i, 0 < x i) ∧ cubeForm d x ≤ X ∧
      (∀ i, (x i : ZMod M) = r i)} =>
    hrepr x.val x.property.1 x.property.2.2
  let e : {x : Fin 3 → ℕ //
      (∀ i, 0 < x i) ∧ cubeForm d x ≤ X ∧
      (∀ i, (x i : ZMod M) = r i)} ≃
      {k : Fin 3 → ℕ //
        cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X} :=
    { toFun := fun x => ⟨toK x, by
        change cubeForm d (fromK (toK x)) ≤ X
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
        have hi := congrArg (fun f : Fin 3 → ℕ => f i) (htoK
          ⟨fromK k.val, ⟨hpos k.val, k.property, hcast k.val⟩⟩)
        change rep i + M * toK _ i = rep i + M * k.val i at hi
        exact Nat.mul_left_cancel (NeZero.pos M) (Nat.add_left_cancel hi) }
  unfold residueNatCount translatedPositiveResidueCount
  exact Nat.card_congr e

theorem fixedPartCount_le_box (d : Fin 3 → ℕ) (M a X : ℕ) :
    fixedPartCount d M a X ≤ Fintype.card (Fin 3 → Fin (X + 1)) := by
  classical
  unfold fixedPartCount
  exact Fintype.card_subtype_le _

theorem localCount_le_box (d : Fin 3 → ℕ) (M a : ℕ) [NeZero M] :
    localCount d M a ≤ Fintype.card (Fin 3 → ZMod M) := by
  classical
  unfold localCount
  exact Fintype.card_subtype_le _

/-- The positive-octant cubic region for fixed coefficients. -/
def cubeRegion (d : Fin 3 → ℕ) : Set (Fin 3 → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ (∑ i, (d i : ℝ) * (t i) ^ 3) ≤ 1}

/-- Its volume, which is the leading constant in the fixed-parts count. -/
noncomputable def fixedPartVolume (d : Fin 3 → ℕ) : ℝ :=
  MeasureTheory.volume.real (cubeRegion d)

theorem cubeRegion_subset_unitCube (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    cubeRegion d ⊆ Set.Icc (0 : Fin 3 → ℝ) 1 := by
  intro t ht
  constructor
  · exact ht.1
  · intro i
    have hnonneg (j : Fin 3) : 0 ≤ (d j : ℝ) * (t j) ^ 3 :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ht.1 j) _)
    have hterm : (d i : ℝ) * (t i) ^ 3 ≤ (1 : ℝ) :=
      (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)).trans ht.2
    have hcoef : (1 : ℝ) ≤ d i := by exact_mod_cast hd i
    have hcube : (t i) ^ 3 ≤ (1 : ℝ) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hcoef) (pow_nonneg (ht.1 i) 3)
      nlinarith
    exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by norm_num) (by simpa using hcube)

theorem cubeRegion_isBounded (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    Bornology.IsBounded (cubeRegion d) :=
  (Metric.isBounded_Icc (0 : Fin 3 → ℝ) 1).subset (cubeRegion_subset_unitCube d hd)

theorem cubeRegion_measurableSet (d : Fin 3 → ℕ) :
    MeasurableSet (cubeRegion d) := by
  have hc : Continuous (fun t : Fin 3 → ℝ => ∑ i, (d i : ℝ) * (t i) ^ 3) := by
    fun_prop
  change MeasurableSet
    (Set.Ici (0 : Fin 3 → ℝ) ∩
      (fun t : Fin 3 → ℝ => ∑ i, (d i : ℝ) * (t i) ^ 3) ⁻¹' Set.Iic 1)
  exact measurableSet_Ici.inter (hc.measurable measurableSet_Iic)

theorem cubeRegion_convex (d : Fin 3 → ℕ) : Convex ℝ (cubeRegion d) := by
  let P : Set (Fin 3 → ℝ) := Set.Ici 0
  have hP : Convex ℝ P := convex_Ici _
  have hi (i : Fin 3) :
      ConvexOn ℝ P (fun t : Fin 3 → ℝ => (d i : ℝ) * (t i) ^ 3) := by
    refine ⟨hP, ?_⟩
    intro x hx y hy a b ha hb hab
    have hpow := (convexOn_pow (𝕜 := ℝ) 3).2 (hx i) (hy i) ha hb hab
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hpow ⊢
    calc
      (d i : ℝ) * (a * x i + b * y i) ^ 3
          ≤ (d i : ℝ) * (a * (x i) ^ 3 + b * (y i) ^ 3) :=
            mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = a * ((d i : ℝ) * (x i) ^ 3) +
            b * ((d i : ℝ) * (y i) ^ 3) := by ring
  have hf :
      ConvexOn ℝ P (fun t : Fin 3 → ℝ => ∑ i, (d i : ℝ) * (t i) ^ 3) := by
    refine ⟨hP, ?_⟩
    intro x hx y hy a b ha hb hab
    calc
      (∑ i, (d i : ℝ) * ((a • x + b • y) i) ^ 3)
          ≤ ∑ i, (a * ((d i : ℝ) * (x i) ^ 3) +
              b * ((d i : ℝ) * (y i) ^ 3)) := by
            apply Finset.sum_le_sum
            intro i _
            simpa only [smul_eq_mul] using (hi i).2 hx hy ha hb hab
      _ = a • (∑ i, (d i : ℝ) * (x i) ^ 3) +
          b • (∑ i, (d i : ℝ) * (y i) ^ 3) := by
            simp [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
  change Convex ℝ {t ∈ P | (∑ i, (d i : ℝ) * (t i) ^ 3) ≤ 1}
  exact hf.convex_le 1

theorem cubeRegion_frontier_null (d : Fin 3 → ℕ) :
    MeasureTheory.volume (frontier (cubeRegion d)) = 0 :=
  Convex.addHaar_frontier MeasureTheory.volume (cubeRegion_convex d)

/-- Within the positive orthant, the cubic region is downward closed in each
coordinate. This gives the lower and upper integer-grid squeeze for residue
vectors. -/
theorem cubeRegion_downward (d : Fin 3 → ℕ) {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : x ≤ y) (hy : y ∈ cubeRegion d) :
    x ∈ cubeRegion d := by
  refine ⟨hx, ?_⟩
  calc
    (∑ i, (d i : ℝ) * (x i) ^ 3)
        ≤ ∑ i, (d i : ℝ) * (y i) ^ 3 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hx i) (hxy i) 3) (Nat.cast_nonneg _)
    _ ≤ 1 := hy.2

theorem fixedPartVolume_pos (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    0 < fixedPartVolume d := by
  let S : ℕ := ∑ i, d i
  let c : ℝ := 1 / ((S : ℝ) + 1)
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (S : ℝ) + 1)).mpr
    linarith
  have hbox : Set.Icc (0 : Fin 3 → ℝ) (fun _ => c) ⊆ cubeRegion d := by
    intro t ht
    constructor
    · exact ht.1
    · have hcube (i : Fin 3) : (t i) ^ 3 ≤ c := by
        have hpow : (t i) ^ 3 ≤ c ^ 3 :=
          pow_le_pow_left₀ (ht.1 i) (ht.2 i) 3
        have hsmall : c ^ 3 ≤ c := by nlinarith [sq_nonneg c]
        exact hpow.trans hsmall
      calc
        (∑ i, (d i : ℝ) * (t i) ^ 3) ≤ ∑ i, (d i : ℝ) * c := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hcube i) (Nat.cast_nonneg _)
        _ = (S : ℝ) * c := by simp [S, Finset.sum_mul]
        _ ≤ 1 := by
          dsimp [c]
          rw [show (S : ℝ) * (1 / ((S : ℝ) + 1)) =
            (S : ℝ) / ((S : ℝ) + 1) by ring]
          exact (div_le_iff₀ (by positivity : (0 : ℝ) < (S : ℝ) + 1)).mpr (by linarith)
  have hfinite : MeasureTheory.volume (cubeRegion d) ≠ ⊤ :=
    (cubeRegion_isBounded d hd).measure_lt_top.ne
  have hboxvol : MeasureTheory.volume.real
      (Set.Icc (0 : Fin 3 → ℝ) (fun _ => c)) = c ^ 3 := by
    change (MeasureTheory.volume (Set.Icc (0 : Fin 3 → ℝ) (fun _ => c))).toReal = c ^ 3
    rw [Real.volume_Icc_pi_toReal]
    · simp
    · exact fun _ => hc_pos.le
  unfold fixedPartVolume
  exact (by rw [hboxvol]; positivity :
    0 < MeasureTheory.volume.real (Set.Icc (0 : Fin 3 → ℝ) (fun _ => c))).trans_le
      (MeasureTheory.measureReal_mono hbox hfinite)

theorem fixedPartVolume_le_one (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    fixedPartVolume d ≤ 1 := by
  unfold fixedPartVolume
  calc
    MeasureTheory.volume.real (cubeRegion d)
        ≤ MeasureTheory.volume.real (Set.Icc (0 : Fin 3 → ℝ) 1) :=
          MeasureTheory.measureReal_mono (cubeRegion_subset_unitCube d hd)
            (by simp [Real.volume_Icc_pi])
    _ = 1 := by
      change (MeasureTheory.volume (Set.Icc (0 : Fin 3 → ℝ) 1)).toReal = 1
      rw [Real.volume_Icc_pi_toReal]
      · simp
      · exact fun _ => zero_le_one

/-- A coefficient-uniform bound on the leading volume. The box containing the
cubic region has side length `dᵢ ^ (-1/3)` in coordinate `i`. -/
theorem fixedPartVolume_le_coeff_product (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    fixedPartVolume d ≤ ∏ i, (d i : ℝ) ^ (-(3 : ℝ)⁻¹) := by
  let b : Fin 3 → ℝ := fun i => (d i : ℝ) ^ (-(3 : ℝ)⁻¹)
  have hb_pos (i : Fin 3) : 0 < b i := by
    dsimp [b]
    have : 0 < (d i : ℝ) := by exact_mod_cast hd i
    positivity
  have hb_cube (i : Fin 3) : b i ^ 3 = (d i : ℝ)⁻¹ := by
    dsimp [b]
    rw [Real.rpow_neg (Nat.cast_nonneg _), inv_pow]
    simpa using
      congrArg Inv.inv (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (d i))
        (by decide : (3 : ℕ) ≠ 0))
  have hbox : cubeRegion d ⊆ Set.Icc (0 : Fin 3 → ℝ) b := by
    intro t ht
    constructor
    · exact ht.1
    · intro i
      have hnonneg (j : Fin 3) : 0 ≤ (d j : ℝ) * (t j) ^ 3 :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ht.1 j) _)
      have hterm : (d i : ℝ) * (t i) ^ 3 ≤ (1 : ℝ) :=
        (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)).trans ht.2
      have hcoef : 0 < (d i : ℝ) := by exact_mod_cast hd i
      have hcube : (t i) ^ 3 ≤ (b i) ^ 3 := by
        rw [hb_cube]
        rw [← one_div]
        exact (le_div_iff₀ hcoef).2 (by nlinarith [hterm])
      exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (hb_pos i).le hcube
  unfold fixedPartVolume
  calc
    MeasureTheory.volume.real (cubeRegion d)
        ≤ MeasureTheory.volume.real (Set.Icc (0 : Fin 3 → ℝ) b) :=
          MeasureTheory.measureReal_mono hbox
            ((Metric.isBounded_Icc (0 : Fin 3 → ℝ) b).measure_lt_top.ne)
    _ = ∏ i, (d i : ℝ) ^ (-(3 : ℝ)⁻¹) := by
      change (MeasureTheory.volume (Set.Icc (0 : Fin 3 → ℝ) b)).toReal = _
      rw [Real.volume_Icc_pi_toReal]
      · simp [b]
      · exact fun i => (hb_pos i).le

/-- The ordinary integer grid has the expected density in the cubic region.
This is the unshifted lattice limit used in the residue-class argument. -/
theorem cubeRegion_lattice_limit (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card ↑(cubeRegion d ∩
          (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))) : ℝ) /
          (n : ℝ) ^ 3)
      Filter.atTop (nhds (fixedPartVolume d)) := by
  simpa [fixedPartVolume] using
    (tendsto_card_div_pow_atTop_volume (s := cubeRegion d)
      (cubeRegion_isBounded d hd) (cubeRegion_measurableSet d)
      (cubeRegion_frontier_null d))

/-- A nonnegative integer vector, scaled by `n`, is in the standard lattice. -/
private theorem gridPoint_mem_lattice (n : ℕ) [NeZero n] (k : Fin 3 → ℕ) :
    (fun i => (k i : ℝ) / n) ∈
      (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))) := by
  apply (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).2
  intro i
  refine ⟨(k i : ℤ), ?_⟩
  simp [mul_div_cancel₀, NeZero.ne n]

/-- Conversely, a lattice point in the nonnegative orthant has nonnegative
integer coordinates after scaling. -/
private theorem exists_nat_of_gridPoint (n : ℕ) [NeZero n]
    (v : Fin 3 → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hgrid : v ∈ (n : ℝ)⁻¹ •
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))) :
    ∃ k : Fin 3 → ℕ, (fun i => (k i : ℝ) / n) = v := by
  have h := (BoxIntegral.unitPartition.mem_smul_span_iff (n := n)).1 hgrid
  choose z hz using h
  have hz' (i : Fin 3) : (z i : ℝ) = (n : ℝ) * v i := by
    simpa using hz i
  have hz_nonneg (i : Fin 3) : 0 ≤ z i := by
    have hreal : 0 ≤ (z i : ℝ) := by
      rw [hz' i]
      exact mul_nonneg (Nat.cast_nonneg _) (hv i)
    exact_mod_cast hreal
  refine ⟨fun i => (z i).toNat, funext fun i => ?_⟩
  have hzi : ((z i).toNat : ℝ) = (z i : ℝ) := by
    exact_mod_cast (Int.natCast_toNat_eq_self.mpr (hz_nonneg i))
  rw [hzi, hz' i]
  exact mul_div_cancel_left₀ (v i) (Nat.cast_ne_zero.mpr (NeZero.ne n))

private theorem gridPoint_mem_cubeRegion_iff (d : Fin 3 → ℕ) (n : ℕ) [NeZero n]
    (k : Fin 3 → ℕ) :
    (fun i => (k i : ℝ) / n) ∈ cubeRegion d ↔ cubeForm d k ≤ n ^ 3 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsum :
      (∑ i, (d i : ℝ) * ((k i : ℝ) / n) ^ 3) =
        (cubeForm d k : ℝ) / (n : ℝ) ^ 3 := by
    calc
      _ = ∑ i, ((d i : ℝ) * (k i : ℝ) ^ 3) / (n : ℝ) ^ 3 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_pow]
        ring
      _ = (cubeForm d k : ℝ) / (n : ℝ) ^ 3 := by
        rw [← Finset.sum_div]
        simp [cubeForm]
  rw [cubeRegion, Set.mem_ofPred_eq, hsum]
  have hnonneg : ∀ i, (0 : ℝ) ≤ (k i : ℝ) / n :=
    fun i => div_nonneg (Nat.cast_nonneg _) hn.le
  constructor
  · intro h
    have hh := h.2
    rw [div_le_iff₀ (pow_pos hn 3), one_mul] at hh
    exact_mod_cast hh
  · intro h
    refine ⟨hnonneg, ?_⟩
    rw [div_le_iff₀ (pow_pos hn 3), one_mul]
    exact_mod_cast h

/-- The standard lattice count is exactly the count of nonnegative natural
triples whose cubic form is at most `n³`. -/
private theorem natGridCount_eq_latticeCount (d : Fin 3 → ℕ) (n : ℕ) [NeZero n] :
    Nat.card {k : Fin 3 → ℕ // cubeForm d k ≤ n ^ 3} =
      Nat.card ↑(cubeRegion d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))) := by
  let f : {k : Fin 3 → ℕ // cubeForm d k ≤ n ^ 3} →
      ↑(cubeRegion d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))) :=
    fun k => ⟨fun i => (k.val i : ℝ) / n,
      ⟨(gridPoint_mem_cubeRegion_iff d n k.val).2 k.property,
        gridPoint_mem_lattice n k.val⟩⟩
  have hf_inj : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun v : Fin 3 → ℝ => v i) (congrArg Subtype.val h)
    change (k.val i : ℝ) / n = (l.val i : ℝ) / n at hi
    exact_mod_cast (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne n))).1 hi
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨k, hk⟩ := exists_nat_of_gridPoint n v.val v.property.1.1 v.property.2
    have hform : cubeForm d k ≤ n ^ 3 :=
      (gridPoint_mem_cubeRegion_iff d n k).1 (hk.symm ▸ v.property.1)
    refine ⟨⟨k, hform⟩, ?_⟩
    apply Subtype.ext
    exact hk
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)

private theorem natGridCount_limit (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {k : Fin 3 → ℕ // cubeForm d k ≤ n ^ 3} : ℝ) / (n : ℝ) ^ 3)
      Filter.atTop (nhds (fixedPartVolume d)) := by
  refine (cubeRegion_lattice_limit d hd).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact congrArg (fun c : ℕ => (c : ℝ) / (n : ℝ) ^ 3)
    (natGridCount_eq_latticeCount d n).symm

/-- The same cubic region with all three coordinates strictly positive. -/
private def cubeRegionPos (d : Fin 3 → ℕ) : Set (Fin 3 → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ (∑ i, (d i : ℝ) * (t i) ^ 3) ≤ 1}

private theorem cubeRegionPos_eq (d : Fin 3 → ℕ) :
    cubeRegionPos d = cubeRegion d ∩
      Set.univ.pi (fun _ : Fin 3 => Set.Ioi (0 : ℝ)) := by
  ext t
  constructor
  · intro ht
    exact ⟨⟨fun i => (ht.1 i).le, ht.2⟩, by simpa [Set.mem_pi] using ht.1⟩
  · rintro ⟨ht, hp⟩
    exact ⟨by simpa [Set.mem_pi] using hp, ht.2⟩

private theorem cubeRegionPos_bounded (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    Bornology.IsBounded (cubeRegionPos d) := by
  apply (cubeRegion_isBounded d hd).subset
  intro t ht
  exact ⟨fun i => (ht.1 i).le, ht.2⟩

private theorem cubeRegionPos_measurable (d : Fin 3 → ℕ) :
    MeasurableSet (cubeRegionPos d) := by
  rw [cubeRegionPos_eq]
  exact (cubeRegion_measurableSet d).inter
    ((isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)).measurableSet)

private theorem cubeRegionPos_convex (d : Fin 3 → ℕ) :
    Convex ℝ (cubeRegionPos d) := by
  rw [cubeRegionPos_eq]
  exact (cubeRegion_convex d).inter
    (convex_pi (fun _ _ => convex_Ioi (0 : ℝ)))

private theorem cubeRegionPos_frontier_null (d : Fin 3 → ℕ) :
    MeasureTheory.volume (frontier (cubeRegionPos d)) = 0 :=
  Convex.addHaar_frontier MeasureTheory.volume (cubeRegionPos_convex d)

private theorem cubeRegionPos_volume_eq (d : Fin 3 → ℕ) :
    MeasureTheory.volume (cubeRegionPos d) = MeasureTheory.volume (cubeRegion d) := by
  have hsub : cubeRegionPos d ⊆ cubeRegion d := by
    intro t ht
    exact ⟨fun i => (ht.1 i).le, ht.2⟩
  have hdiff : cubeRegion d \ cubeRegionPos d ⊆
      ⋃ i : Fin 3, {t : Fin 3 → ℝ | t i = 0} := by
    intro t ht
    have hnot : ¬∀ i, 0 < t i := by
      intro hp
      exact ht.2 ⟨hp, ht.1.2⟩
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    exact le_antisymm (le_of_not_gt hi) (ht.1.1 i)
  have hzero : MeasureTheory.volume
      (⋃ i : Fin 3, {t : Fin 3 → ℝ | t i = 0}) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro i
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => MeasureTheory.volume) i 0
  exact MeasureTheory.measure_eq_measure_of_null_sdiff hsub
    (MeasureTheory.measure_mono_null hdiff hzero)

private theorem gridPoint_mem_cubeRegionPos_iff (d : Fin 3 → ℕ)
    (n : ℕ) [NeZero n] (k : Fin 3 → ℕ) :
    (fun i => (k i : ℝ) / n) ∈ cubeRegionPos d ↔
      (∀ i, 0 < k i) ∧ cubeForm d k ≤ n ^ 3 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  rw [cubeRegionPos_eq, Set.mem_inter_iff, gridPoint_mem_cubeRegion_iff]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioi]
  constructor
  · rintro ⟨hform, hp⟩
    exact ⟨fun i => by
      have hi : (0 : ℝ) < (k i : ℝ) := by
        simpa using (lt_div_iff₀ hn).1 (hp i)
      exact_mod_cast hi, hform⟩
  · rintro ⟨hp, hform⟩
    exact ⟨hform, fun i => div_pos (by exact_mod_cast hp i) hn⟩

private theorem natGridPosCount_eq_latticeCount (d : Fin 3 → ℕ)
    (n : ℕ) [NeZero n] :
    Nat.card {k : Fin 3 → ℕ // (∀ i, 0 < k i) ∧ cubeForm d k ≤ n ^ 3} =
      Nat.card ↑(cubeRegionPos d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))) := by
  let f : {k : Fin 3 → ℕ // (∀ i, 0 < k i) ∧ cubeForm d k ≤ n ^ 3} →
      ↑(cubeRegionPos d ∩
        (n : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))) :=
    fun k => ⟨fun i => (k.val i : ℝ) / n,
      ⟨(gridPoint_mem_cubeRegionPos_iff d n k.val).2 k.property,
        gridPoint_mem_lattice n k.val⟩⟩
  have hf_inj : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    have hi := congrArg (fun v : Fin 3 → ℝ => v i) (congrArg Subtype.val h)
    change (k.val i : ℝ) / n = (l.val i : ℝ) / n at hi
    exact_mod_cast (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne n))).1 hi
  have hf_surj : Function.Surjective f := by
    intro v
    obtain ⟨k, hk⟩ := exists_nat_of_gridPoint n v.val
      (fun i => (v.property.1.1 i).le) v.property.2
    have hform : (∀ i, 0 < k i) ∧ cubeForm d k ≤ n ^ 3 :=
      (gridPoint_mem_cubeRegionPos_iff d n k).1 (hk.symm ▸ v.property.1)
    refine ⟨⟨k, hform⟩, ?_⟩
    apply Subtype.ext
    exact hk
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)

private theorem natGridPosCount_limit (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {k : Fin 3 → ℕ // (∀ i, 0 < k i) ∧ cubeForm d k ≤ n ^ 3} : ℝ) /
          (n : ℝ) ^ 3)
      Filter.atTop (nhds (fixedPartVolume d)) := by
  have h := tendsto_card_div_pow_atTop_volume (s := cubeRegionPos d)
    (cubeRegionPos_bounded d hd) (cubeRegionPos_measurable d)
    (cubeRegionPos_frontier_null d)
  have hv : MeasureTheory.volume.real (cubeRegionPos d) = fixedPartVolume d := by
    simp [fixedPartVolume, MeasureTheory.Measure.real, cubeRegionPos_volume_eq]
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact congrArg (fun c : ℕ => (c : ℝ) / (n : ℝ) ^ 3)
    (natGridPosCount_eq_latticeCount d n).symm

private theorem finite_cubeForm_sublevel (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (X : ℕ) :
    Finite {x : Fin 3 → ℕ // cubeForm d x ≤ X} := by
  let f : {x : Fin 3 → ℕ // cubeForm d x ≤ X} → Fin 3 → Fin (X + 1) :=
    fun x i => ⟨x.val i, Nat.lt_succ_of_le ((cubeForm_coord_le d x.val hd i).trans
      x.property)⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

private theorem finite_translatedPositiveResidueCount (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (M X : ℕ) [NeZero M]
    (r : Fin 3 → ZMod M) :
    Finite {k : Fin 3 → ℕ //
      cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X} := by
  have := finite_cubeForm_sublevel d hd X
  let f : {k : Fin 3 → ℕ //
      cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤ X} →
      {x : Fin 3 → ℕ // cubeForm d x ≤ X} :=
    fun k => ⟨fun i => positiveResidueRep M (r i) + M * k.val i, k.property⟩
  apply Finite.of_injective f
  intro k l h
  apply Subtype.ext
  funext i
  have hi := congrFun (congrArg Subtype.val h) i
  exact Nat.mul_left_cancel (NeZero.pos M) (Nat.add_left_cancel hi)

/-- The positive-representative residue grid is squeezed between the
positive and nonnegative ordinary grids at cube cutoffs. -/
private theorem translatedPositiveResidueCount_bounds (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (M n : ℕ) [NeZero M]
    (r : Fin 3 → ZMod M) :
    Nat.card {j : Fin 3 → ℕ // (∀ i, 0 < j i) ∧ cubeForm d j ≤ n ^ 3} ≤
      translatedPositiveResidueCount d M ((M * n) ^ 3) r ∧
    translatedPositiveResidueCount d M ((M * n) ^ 3) r ≤
      Nat.card {j : Fin 3 → ℕ // cubeForm d j ≤ n ^ 3} := by
  classical
  have := finite_translatedPositiveResidueCount d hd M ((M * n) ^ 3) r
  have := finite_cubeForm_sublevel d hd (n ^ 3)
  have hupper : translatedPositiveResidueCount d M ((M * n) ^ 3) r ≤
      Nat.card {j : Fin 3 → ℕ // cubeForm d j ≤ n ^ 3} := by
    let f : {k : Fin 3 → ℕ //
        cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤
          (M * n) ^ 3} →
        {j : Fin 3 → ℕ // cubeForm d j ≤ n ^ 3} :=
      fun k => ⟨k.val, by
        have hc : cubeForm d (fun i => M * k.val i) ≤
            cubeForm d (fun i => positiveResidueRep M (r i) + M * k.val i) :=
          cubeForm_mono d (fun i => Nat.le_add_left _ _)
        rw [cubeForm_nsmul] at hc
        have h := hc.trans k.property
        have h' : M ^ 3 * cubeForm d k.val ≤ M ^ 3 * n ^ 3 := by
          calc
            _ ≤ (M * n) ^ 3 := h
            _ = M ^ 3 * n ^ 3 := mul_pow M n 3
        exact Nat.le_of_mul_le_mul_left h' (pow_pos (NeZero.pos M) 3)⟩
    change Nat.card _ ≤ Nat.card _
    exact Nat.card_le_card_of_injective f (by
      intro k l h
      apply Subtype.ext
      have hh := congrArg (fun z : {j : Fin 3 → ℕ // cubeForm d j ≤ n ^ 3} => z.val) h
      exact hh)
  have hlower :
      Nat.card {j : Fin 3 → ℕ // (∀ i, 0 < j i) ∧ cubeForm d j ≤ n ^ 3} ≤
      translatedPositiveResidueCount d M ((M * n) ^ 3) r := by
    let f : {j : Fin 3 → ℕ // (∀ i, 0 < j i) ∧ cubeForm d j ≤ n ^ 3} →
        {k : Fin 3 → ℕ //
          cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤
            (M * n) ^ 3} :=
      fun j => ⟨fun i => j.val i - 1, by
        have hc : cubeForm d (fun i => positiveResidueRep M (r i) +
              M * (j.val i - 1)) ≤ cubeForm d (fun i => M * j.val i) := by
          apply cubeForm_mono d
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
        rw [cubeForm_nsmul] at hc
        calc
          _ ≤ M ^ 3 * cubeForm d j.val := hc
          _ ≤ M ^ 3 * n ^ 3 := Nat.mul_le_mul_left _ j.property.2
          _ = (M * n) ^ 3 := by ring⟩
    change Nat.card _ ≤ Nat.card _
    exact Nat.card_le_card_of_injective f (by
      intro j l h
      apply Subtype.ext
      funext i
      have hi := congrFun (congrArg (fun z : {k : Fin 3 → ℕ //
        cubeForm d (fun i => positiveResidueRep M (r i) + M * k i) ≤
          (M * n) ^ 3} => z.val) h) i
      have hj : j.val i = (j.val i - 1) + 1 :=
        (Nat.sub_add_cancel (j.property.1 i)).symm
      have hl : l.val i = (l.val i - 1) + 1 :=
        (Nat.sub_add_cancel (l.property.1 i)).symm
      change j.val i - 1 = l.val i - 1 at hi
      omega)
  exact ⟨hlower, hupper⟩

/-- Along cube cutoffs, the fixed-residue count has the expected density. -/
private theorem residueVector_cube_asymptotic (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (M : ℕ) [NeZero M]
    (r : Fin 3 → ZMod M) :
    Filter.Tendsto
      (fun n : ℕ =>
        (residueVectorCount d M ((M * n) ^ 3) r : ℝ) / ((M * n : ℕ) : ℝ) ^ 3)
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 3)) := by
  have hpos : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {j : Fin 3 → ℕ // (∀ i, 0 < j i) ∧ cubeForm d j ≤ n ^ 3} : ℝ) /
          ((M * n : ℕ) : ℝ) ^ 3)
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 3)) := by
    convert (natGridPosCount_limit d hd).div_const ((M : ℝ) ^ 3) using 1
    funext n
    simp only [Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  have hnon : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {j : Fin 3 → ℕ // cubeForm d j ≤ n ^ 3} : ℝ) /
          ((M * n : ℕ) : ℝ) ^ 3)
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 3)) := by
    convert (natGridCount_limit d hd).div_const ((M : ℝ) ^ 3) using 1
    funext n
    simp only [Nat.cast_mul, mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  refine Filter.Tendsto.squeeze' hpos hnon ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hden : (0 : ℝ) < ((M * n : ℕ) : ℝ) ^ 3 := by
      exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos M) hn) 3
    have hbound := (translatedPositiveResidueCount_bounds d hd M n r).1
    have hcount : residueVectorCount d M ((M * n) ^ 3) r =
        translatedPositiveResidueCount d M ((M * n) ^ 3) r :=
      (residueVectorCount_eq_residueNatCount d hd M _ r).trans
        (residueNatCount_eq_translatedPositiveResidueCount d M _ r)
    rw [hcount]
    exact (div_le_div_iff_of_pos_right hden).2 (by exact_mod_cast hbound)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hden : (0 : ℝ) < ((M * n : ℕ) : ℝ) ^ 3 := by
      exact_mod_cast pow_pos (Nat.mul_pos (NeZero.pos M) hn) 3
    have hbound := (translatedPositiveResidueCount_bounds d hd M n r).2
    have hcount : residueVectorCount d M ((M * n) ^ 3) r =
        translatedPositiveResidueCount d M ((M * n) ^ 3) r :=
      (residueVectorCount_eq_residueNatCount d hd M _ r).trans
        (residueNatCount_eq_translatedPositiveResidueCount d M _ r)
    rw [hcount]
    exact (div_le_div_iff_of_pos_right hden).2 (by exact_mod_cast hbound)

private def cubeCutoffIndex (M X : ℕ) : ℕ := Nat.nthRoot 3 X / M

private theorem cubeCutoffIndex_bracket (M X : ℕ) [NeZero M] :
    (M * cubeCutoffIndex M X) ^ 3 ≤ X ∧
      X < (M * (cubeCutoffIndex M X + 1)) ^ 3 := by
  let q := Nat.nthRoot 3 X
  have hleft : M * (q / M) ≤ q := by
    simpa [mul_comm] using Nat.div_mul_le_self q M
  have hright : q < M * (q / M + 1) := by
    simpa [mul_comm] using
      (Nat.div_lt_iff_lt_mul (NeZero.pos M)).1 (Nat.lt_succ_self (q / M))
  change (M * (q / M)) ^ 3 ≤ X ∧ X < (M * (q / M + 1)) ^ 3
  constructor
  · exact (pow_le_pow_left₀ (Nat.zero_le _) hleft 3).trans
      (Nat.pow_nthRoot_le (.inl (by decide : (3 : ℕ) ≠ 0)))
  · exact (Nat.lt_pow_nthRoot_add_one (by decide : (3 : ℕ) ≠ 0) X).trans_le
      (pow_le_pow_left₀ (Nat.zero_le _)
        (Nat.succ_le_iff.mpr hright) 3)

private theorem cubeCutoffIndex_tendsto (M : ℕ) [NeZero M] :
    Filter.Tendsto (cubeCutoffIndex M) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop ((M * b) ^ 3)] with X hX
  have hroot : M * b ≤ Nat.nthRoot 3 X :=
    (Nat.le_nthRoot_iff (by decide : (3 : ℕ) ≠ 0)).2 hX
  exact (Nat.le_div_iff_mul_le (NeZero.pos M)).2 (by
    simpa [cubeCutoffIndex, mul_comm] using hroot)

private theorem cubeCutoff_ratio_tendsto (M : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun n : ℕ => (((M * n : ℕ) : ℝ) ^ 3) /
        (((M * (n + 1) : ℕ) : ℝ) ^ 3))
      Filter.atTop (nhds (1 : ℝ)) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).pow 3
  simpa only [one_pow] using h.congr' (by
    filter_upwards [] with n
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_pow]
    field_simp)

private theorem cubeCutoff_inv_ratio_tendsto (M : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun n : ℕ => (((M * (n + 1) : ℕ) : ℝ) ^ 3) /
        (((M * n : ℕ) : ℝ) ^ 3))
      Filter.atTop (nhds (1 : ℝ)) := by
  have h := (cubeCutoff_ratio_tendsto M).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_one] using h.congr' (by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    simp only [inv_div])

/-- The fixed-residue count is monotone in its cutoff. -/
theorem residueVectorCount_mono (d : Fin 3 → ℕ) (M : ℕ)
    (r : Fin 3 → ZMod M) : Monotone (fun X => residueVectorCount d M X r) := by
  classical
  intro X Y hXY
  unfold residueVectorCount
  let e : Fin (X + 1) ↪ Fin (Y + 1) :=
    ⟨Fin.castLE (Nat.succ_le_succ hXY),
      Fin.castLE_injective (Nat.succ_le_succ hXY)⟩
  let f : {x : Fin 3 → Fin (X + 1) //
      (∀ i, 0 < (x i).val) ∧
      cubeForm d (fun i => (x i).val) ≤ X ∧
      (∀ i, ((x i).val : ZMod M) = r i)} ↪
      {x : Fin 3 → Fin (Y + 1) //
        (∀ i, 0 < (x i).val) ∧
        cubeForm d (fun i => (x i).val) ≤ Y ∧
        (∀ i, ((x i).val : ZMod M) = r i)} :=
    ⟨fun x => ⟨fun i => e (x.val i), by
      have hv (i : Fin 3) : (e (x.val i)).val = (x.val i).val := rfl
      simp only [hv]
      exact ⟨x.property.1, x.property.2.1.trans hXY, x.property.2.2⟩⟩, by
      intro x y h
      apply Subtype.ext
      funext i
      exact e.injective (congrArg (fun z : Fin 3 → Fin (Y + 1) => z i)
        (congrArg Subtype.val h))⟩
  exact Fintype.card_le_of_injective f f.injective

/-- The lattice-point principle applied to one fixed residue vector. The
limit is the consequence of Proposition 4.1 needed by the density argument. -/
theorem residueVector_asymptotic (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (M : ℕ) [NeZero M]
    (r : Fin 3 → ZMod M) :
    Filter.Tendsto
      (fun X : ℕ => (residueVectorCount d M X r : ℝ) / (X : ℝ))
      Filter.atTop (nhds (fixedPartVolume d / (M : ℝ) ^ 3)) := by
  let F : ℕ → ℕ := fun X => residueVectorCount d M X r
  let g : ℕ → ℕ := fun n => (M * n) ^ 3
  let N : ℕ → ℕ := cubeCutoffIndex M
  let C : ℝ := fixedPartVolume d / (M : ℝ) ^ 3
  have hcube : Filter.Tendsto
      (fun n : ℕ => (F (g n) : ℝ) / (g n : ℝ)) Filter.atTop (nhds C) := by
    simpa [F, g, C] using residueVector_cube_asymptotic d hd M r
  have hN : Filter.Tendsto N Filter.atTop Filter.atTop := cubeCutoffIndex_tendsto M
  have hNsucc : Filter.Tendsto (fun X => N X + 1) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp hN
  have hlow : Filter.Tendsto
      (fun X : ℕ => (F (g (N X)) : ℝ) / (g (N X + 1) : ℝ))
      Filter.atTop (nhds C) := by
    have hprod := (hcube.comp hN).mul ((cubeCutoff_ratio_tendsto M).comp hN)
    have hprod' : Filter.Tendsto
        (fun X : ℕ => ((F (g (N X)) : ℝ) / (g (N X) : ℝ)) *
          ((g (N X) : ℝ) / (g (N X + 1) : ℝ)))
        Filter.atTop (nhds C) := by
      simpa [g, C] using hprod
    refine hprod'.congr' ?_
    filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hgn : (g (N X) : ℝ) ≠ 0 := by
      have h : 0 < g (N X) := pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 3
      exact_mod_cast h.ne'
    have hgn1 : (g (N X + 1) : ℝ) ≠ 0 := by
      have h : 0 < g (N X + 1) :=
        pow_pos (Nat.mul_pos (NeZero.pos M) (Nat.succ_pos _)) 3
      exact_mod_cast h.ne'
    field_simp
  have hupp : Filter.Tendsto
      (fun X : ℕ => (F (g (N X + 1)) : ℝ) / (g (N X) : ℝ))
      Filter.atTop (nhds C) := by
    have hprod := (hcube.comp hNsucc).mul ((cubeCutoff_inv_ratio_tendsto M).comp hN)
    have hprod' : Filter.Tendsto
        (fun X : ℕ => ((F (g (N X + 1)) : ℝ) / (g (N X + 1) : ℝ)) *
          ((g (N X + 1) : ℝ) / (g (N X) : ℝ)))
        Filter.atTop (nhds C) := by
      simpa [g, C] using hprod
    refine hprod'.congr' ?_
    filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hgn : (g (N X) : ℝ) ≠ 0 := by
      have h : 0 < g (N X) := pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 3
      exact_mod_cast h.ne'
    have hgn1 : (g (N X + 1) : ℝ) ≠ 0 := by
      have h : 0 < g (N X + 1) :=
        pow_pos (Nat.mul_pos (NeZero.pos M) (Nat.succ_pos _)) 3
      exact_mod_cast h.ne'
    field_simp
  change Filter.Tendsto (fun X => (F X : ℝ) / (X : ℝ)) Filter.atTop (nhds C)
  refine Filter.Tendsto.squeeze' hlow hupp ?_ ?_
  · filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hbr : g (N X) ≤ X ∧ X < g (N X + 1) :=
      cubeCutoffIndex_bracket M X
    have hX : 0 < X := (pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 3).trans_le hbr.1
    have hg1 : 0 < g (N X + 1) :=
      pow_pos (Nat.mul_pos (NeZero.pos M) (Nat.succ_pos _)) 3
    have hF : F (g (N X)) ≤ F X := residueVectorCount_mono d M r hbr.1
    have hcross : F (g (N X)) * X ≤ F X * g (N X + 1) := by
      calc
        _ ≤ F (g (N X)) * g (N X + 1) := Nat.mul_le_mul_left _ hbr.2.le
        _ ≤ F X * g (N X + 1) := Nat.mul_le_mul_right _ hF
    exact (div_le_div_iff₀ (by exact_mod_cast hg1) (by exact_mod_cast hX)).2
      (by exact_mod_cast hcross)
  · filter_upwards [hN.eventually (Filter.eventually_gt_atTop (0 : ℕ))] with X hNX
    have hbr : g (N X) ≤ X ∧ X < g (N X + 1) :=
      cubeCutoffIndex_bracket M X
    have hX : 0 < X := (pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 3).trans_le hbr.1
    have hg0 : 0 < g (N X) := pow_pos (Nat.mul_pos (NeZero.pos M) hNX) 3
    have hF : F X ≤ F (g (N X + 1)) := residueVectorCount_mono d M r hbr.2.le
    have hcross : F X * g (N X) ≤ F (g (N X + 1)) * X := by
      calc
        _ ≤ F X * X := Nat.mul_le_mul_left _ hbr.1
        _ ≤ F (g (N X + 1)) * X := Nat.mul_le_mul_right _ hF
    exact (div_le_div_iff₀ (by exact_mod_cast hX) (by exact_mod_cast hg0)).2
      (by exact_mod_cast hcross)

/-- For coprime moduli, the number of admissible residue vectors factors.
The proof should use `ZMod.chineseRemainder` coordinatewise. -/
theorem localCount_mul_of_coprime (d : Fin 3 → ℕ) (m n a : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcoprime : m.Coprime n) :
    localCount d (m * n) a = localCount d m a * localCount d n a := by
  classical
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcoprime
  let E : (Fin 3 → ZMod (m * n)) ≃
      (Fin 3 → ZMod m) × (Fin 3 → ZMod n) :=
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
  have he_form (x : Fin 3 → ZMod (m * n)) :
      e (cubeFormMod (m * n) d x) =
        (cubeFormMod m d (E x).1, cubeFormMod n d (E x).2) := by
    apply Prod.ext
    · simp [cubeFormMod, E, Prod.fst_sum]
    · simp [cubeFormMod, E, Prod.snd_sum]
  have hp (x : Fin 3 → ZMod (m * n)) :
      cubeFormMod (m * n) d x = (a : ZMod (m * n)) ↔
        cubeFormMod m d (E x).1 = (a : ZMod m) ∧
          cubeFormMod n d (E x).2 = (a : ZMod n) := by
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
      {x : Fin 3 → ZMod (m * n) // cubeFormMod (m * n) d x = (a : ZMod (m * n))} ≃
      {yz : (Fin 3 → ZMod m) × (Fin 3 → ZMod n) //
        cubeFormMod m d yz.1 = (a : ZMod m) ∧
          cubeFormMod n d yz.2 = (a : ZMod n)} :=
    E.subtypeEquiv hp
  let Eprod :
      {x : Fin 3 → ZMod (m * n) // cubeFormMod (m * n) d x = (a : ZMod (m * n))} ≃
        {x : Fin 3 → ZMod m // cubeFormMod m d x = (a : ZMod m)} ×
        {x : Fin 3 → ZMod n // cubeFormMod n d x = (a : ZMod n)} :=
    Esub.trans (Equiv.subtypeProdEquivProd
      (p := fun x : Fin 3 → ZMod m => cubeFormMod m d x = (a : ZMod m))
      (q := fun x : Fin 3 → ZMod n => cubeFormMod n d x = (a : ZMod n)))
  exact (Fintype.card_congr Eprod).trans (by simp [localCount])

/-- The bounded count is the sum of its residue-vector fibers. -/
theorem fixedPartCount_eq_sum_residueVectorCount (d : Fin 3 → ℕ)
    (M a X : ℕ) [NeZero M] :
    fixedPartCount d M a X =
      ∑ r ∈ (Finset.univ.filter fun r : Fin 3 → ZMod M =>
        cubeFormMod M d r = (a : ZMod M)), residueVectorCount d M X r := by
  classical
  let B : Finset (Fin 3 → Fin (X + 1)) :=
    Finset.univ.filter fun x =>
      (∀ i, 0 < (x i).val) ∧ cubeForm d (fun i => (x i).val) ≤ X
  let T : Finset (Fin 3 → ZMod M) :=
    Finset.univ.filter fun r => cubeFormMod M d r = (a : ZMod M)
  let R : (Fin 3 → Fin (X + 1)) → (Fin 3 → ZMod M) :=
    fun x i => ((x i).val : ZMod M)
  have hfull : (B.filter fun x => R x ∈ T).card = fixedPartCount d M a X := by
    simp [B, T, R, fixedPartCount, Fintype.card_subtype,
      Finset.filter_filter, cubeForm_cast, and_assoc]
  have hfiber (r : Fin 3 → ZMod M) :
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

/-- Proposition 4.1 in the limit form needed by the density argument. It
follows by summing the residue-vector limits over the finitely many admissible
vectors. -/
theorem fixedPartCount_asymptotic (d : Fin 3 → ℕ)
    (hd : ∀ i, 0 < d i) (M a : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun X : ℕ => (fixedPartCount d M a X : ℝ) / (X : ℝ))
      Filter.atTop
      (nhds (fixedPartVolume d * (localCount d M a : ℝ) / (M : ℝ) ^ 3)) := by
  classical
  let T : Finset (Fin 3 → ZMod M) :=
    Finset.univ.filter fun r => cubeFormMod M d r = (a : ZMod M)
  have hsum :
      Filter.Tendsto
        (fun X : ℕ => ∑ r ∈ T, (residueVectorCount d M X r : ℝ) / (X : ℝ))
        Filter.atTop
        (nhds (∑ r ∈ T, fixedPartVolume d / (M : ℝ) ^ 3)) :=
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
      (∑ r ∈ T, fixedPartVolume d / (M : ℝ) ^ 3) =
        fixedPartVolume d * (localCount d M a : ℝ) / (M : ℝ) ^ 3 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hcard]
    ring
  rw [← hfun, hlimit] at hsum
  exact hsum

end Erdos940
