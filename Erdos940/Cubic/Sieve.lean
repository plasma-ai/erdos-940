module

public import Erdos940.Cubic.Parts
public import Erdos940.Cubic.FixedParts
public import Erdos940.Cubic.Progression
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Find

/-!
# Finite truncation of three cube-full summands

The finite part of the sieve in Beyer–de Ryke, Sections 2, 4 and 5. Counts of
distinct represented values are bounded by ordered representations. The latter
are separated according to whether their canonical parts lie in `D³`, in
`E³ \ D³`, or outside `E³`. Analytic estimates for those three terms belong in
other modules.
-/

@[expose] public section

namespace Erdos940

open Finset

/-- Canonical parts no larger than `X`, enumerated without assuming that all
natural numbers are canonical parts. -/
noncomputable def partsBelow (X : ℕ) : Finset CanonicalParts := by
  classical
  exact (((range (X + 1)).filter CanonicalPart).attach).image
    (fun n => (⟨n.1, (mem_filter.mp n.2).2⟩ : CanonicalParts))

theorem mem_partsBelow {X : ℕ} {d : CanonicalParts} :
    d ∈ partsBelow X ↔ d.val ≤ X := by
  classical
  constructor
  · intro hd
    unfold partsBelow at hd
    obtain ⟨n, hn, hdn⟩ := mem_image.mp hd
    have hn' := (mem_filter.mp n.2).1
    have heq : d.val = n.1 := congrArg Subtype.val hdn.symm
    rw [heq]
    exact Nat.lt_succ_iff.mp (mem_range.mp hn')
  · intro hd
    unfold partsBelow
    apply mem_image.mpr
    let n : {n : ℕ // n ∈ (range (X + 1)).filter CanonicalPart} :=
      ⟨d.val, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_iff.mpr hd), d.property⟩⟩
    refine ⟨n, mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

/-- Ordered triples of parts selected from a finite family. -/
noncomputable def partTriples (D : Finset CanonicalParts) :
    Finset (Fin 3 → CanonicalParts) := by
  classical
  exact Fintype.piFinset (fun _ : Fin 3 => D)

theorem mem_partTriples {D : Finset CanonicalParts} {d : Fin 3 → CanonicalParts} :
    d ∈ partTriples D ↔ ∀ i, d i ∈ D := by
  classical
  simp [partTriples, Fintype.mem_piFinset]

/-- Root triples counted for a particular ordered triple of parts. -/
noncomputable def rootTriples (d : Fin 3 → CanonicalParts) (M a X : ℕ) :
    Finset (Fin 3 → Fin (X + 1)) := by
  classical
  exact univ.filter fun x =>
    (∀ i, 0 < (x i).val) ∧
      cubeForm (fun i => (d i).val) (fun i => (x i).val) ≤ X ∧
      (cubeForm (fun i => (d i).val) (fun i => (x i).val) : ZMod M) =
        (a : ZMod M)

theorem rootTriples_card (d : Fin 3 → CanonicalParts) (M a X : ℕ) :
    (rootTriples d M a X).card = fixedPartCount (fun i => (d i).val) M a X := by
  classical
  simp [rootTriples, fixedPartCount, Fintype.card_subtype]

/-- Values with an ordered representation whose parts lie in `D`. -/
noncomputable def representedWithParts (D : Finset CanonicalParts)
    (M a X : ℕ) : Finset ℕ := by
  classical
  exact (partTriples D).biUnion fun d =>
    (rootTriples d M a X).image
      (fun x => cubeForm (fun i => (d i).val) (fun i => (x i).val))

theorem representedWithParts_card_le (D : Finset CanonicalParts)
    (M a X : ℕ) :
    (representedWithParts D M a X).card ≤
      ∑ d ∈ partTriples D, fixedPartCount (fun i => (d i).val) M a X := by
  classical
  unfold representedWithParts
  calc
    ((partTriples D).biUnion fun d =>
        (rootTriples d M a X).image
          (fun x => cubeForm (fun i => (d i).val) (fun i => (x i).val))).card
      ≤ ∑ d ∈ partTriples D,
          ((rootTriples d M a X).image
            (fun x => cubeForm (fun i => (d i).val) (fun i => (x i).val))).card :=
        card_biUnion_le
    _ ≤ ∑ d ∈ partTriples D, (rootTriples d M a X).card :=
        sum_le_sum fun _ _ => card_image_le
    _ = ∑ d ∈ partTriples D,
          fixedPartCount (fun i => (d i).val) M a X := by
        apply sum_congr rfl
        intro d _
        exact rootTriples_card d M a X

/-- A `D`/`E` partition of all bounded ordered part triples. -/
theorem partTriples_split (D E : Finset CanonicalParts) (hDE : D ⊆ E) (X : ℕ) :
    partTriples (partsBelow X) =
      (partTriples (partsBelow X) ∩ partTriples D) ∪
      (partTriples (partsBelow X) ∩ (partTriples E \ partTriples D)) ∪
      (partTriples (partsBelow X) \ partTriples E) := by
  classical
  have hsub : partTriples D ⊆ partTriples E := by
    intro d hd
    exact mem_partTriples.mpr (fun i => hDE ((mem_partTriples.mp hd) i))
  ext d
  by_cases hd : d ∈ partTriples D <;>
    by_cases he : d ∈ partTriples E <;>
    simp_all

/-- The counting function over the finite part box, separated into the three
regions used in Section 5. This is a finite identity, with no local-density
or asymptotic estimate. -/
theorem fixedPartCount_split (D E : Finset CanonicalParts) (hDE : D ⊆ E)
    (M a X : ℕ) :
    (∑ d ∈ partTriples (partsBelow X),
      fixedPartCount (fun i => (d i).val) M a X) =
    (∑ d ∈ partTriples (partsBelow X) ∩ partTriples D,
      fixedPartCount (fun i => (d i).val) M a X) +
    (∑ d ∈ partTriples (partsBelow X) ∩
        (partTriples E \ partTriples D),
      fixedPartCount (fun i => (d i).val) M a X) +
    (∑ d ∈ partTriples (partsBelow X) \ partTriples E,
      fixedPartCount (fun i => (d i).val) M a X) := by
  classical
  let B := partTriples (partsBelow X)
  let A := B ∩ partTriples D
  let C := B ∩ (partTriples E \ partTriples D)
  let T := B \ partTriples E
  have hsplit : B = (A ∪ C) ∪ T := by
    simpa only [B, A, C, T, union_assoc] using partTriples_split D E hDE X
  have hAC : Disjoint A C := by
    apply disjoint_left.mpr
    intro d hdA hdC
    exact (mem_sdiff.mp (mem_inter.mp hdC).2).2 (mem_inter.mp hdA).2
  have hACT : Disjoint (A ∪ C) T := by
    apply disjoint_left.mpr
    intro d hdAC hdT
    have hnotE := (mem_sdiff.mp hdT).2
    rcases mem_union.mp hdAC with hdA | hdC
    · have hsub : partTriples D ⊆ partTriples E := by
        intro e he
        exact mem_partTriples.mpr (fun i => hDE ((mem_partTriples.mp he) i))
      exact hnotE (hsub (mem_inter.mp hdA).2)
    · exact hnotE (mem_sdiff.mp (mem_inter.mp hdC).2).1
  change (∑ d ∈ B, fixedPartCount (fun i => (d i).val) M a X) =
    (∑ d ∈ A, fixedPartCount (fun i => (d i).val) M a X) +
    (∑ d ∈ C, fixedPartCount (fun i => (d i).val) M a X) +
    (∑ d ∈ T, fixedPartCount (fun i => (d i).val) M a X)
  rw [hsplit, sum_union hACT, sum_union hAC]

private theorem canonicalData_factor_bounds (t : CanonicalData) :
    t.x ≤ t.value ∧ t.b ^ 4 * t.c ^ 5 ≤ t.value := by
  have hx3 : t.x ≤ t.x ^ 3 := le_self_pow₀ t.x_pos (by decide)
  have hx3one : 1 ≤ t.x ^ 3 := pow_pos t.x_pos _
  have hdpos : 1 ≤ t.b ^ 4 * t.c ^ 5 :=
    Nat.mul_pos (pow_pos t.b_pos _) (pow_pos t.c_pos _)
  dsimp [CanonicalData.value]
  constructor
  · calc
      t.x ≤ t.x ^ 3 := hx3
      _ ≤ t.x ^ 3 * (t.b ^ 4 * t.c ^ 5) :=
        le_mul_of_one_le_right (Nat.zero_le _) hdpos
      _ = t.x ^ 3 * t.b ^ 4 * t.c ^ 5 := by ring
  · calc
      t.b ^ 4 * t.c ^ 5 ≤ t.x ^ 3 * (t.b ^ 4 * t.c ^ 5) :=
        le_mul_of_one_le_left (Nat.zero_le _) hx3one
      _ = t.x ^ 3 * t.b ^ 4 * t.c ^ 5 := by ring

/-- An exact three-positive-summand value supplies an ordered canonical
representation. -/
theorem threePositive_has_canonical_data {n : ℕ}
    (hn : ThreePositiveCubeFullSum n) :
    ∃ t₀ t₁ t₂ : CanonicalData, n = t₀.value + t₁.value + t₂.value := by
  obtain ⟨a, b, c, ha, hb, hc, hfa, hfb, hfc, rfl⟩ := hn
  obtain ⟨t₀, rfl⟩ := exists_canonicalData_of_cubeFull a ⟨ha, hfa⟩
  obtain ⟨t₁, rfl⟩ := exists_canonicalData_of_cubeFull b ⟨hb, hfb⟩
  obtain ⟨t₂, rfl⟩ := exists_canonicalData_of_cubeFull c ⟨hc, hfc⟩
  exact ⟨t₀, t₁, t₂, rfl⟩

private theorem represented_of_canonical_data
    (t₀ t₁ t₂ : CanonicalData) (M a X : ℕ)
    (hX : t₀.value + t₁.value + t₂.value ≤ X)
    (hmod : (t₀.value + t₁.value + t₂.value) % M = a) :
    t₀.value + t₁.value + t₂.value ∈
      representedWithParts (partsBelow X) M a X := by
  classical
  let t : Fin 3 → CanonicalData := ![t₀, t₁, t₂]
  let d : Fin 3 → CanonicalParts :=
    fun i => ⟨(t i).b ^ 4 * (t i).c ^ 5, (t i).part⟩
  have hterm (i : Fin 3) : (t i).value ≤ X := by
    fin_cases i <;> dsimp [t] <;> omega
  have hd : d ∈ partTriples (partsBelow X) := by
    apply mem_partTriples.mpr
    intro i
    apply mem_partsBelow.mpr
    exact (canonicalData_factor_bounds (t i)).2.trans (hterm i)
  let x : Fin 3 → Fin (X + 1) :=
    fun i => ⟨(t i).x, Nat.lt_succ_of_le
      ((canonicalData_factor_bounds (t i)).1.trans (hterm i))⟩
  have hform :
      cubeForm (fun i => (d i).val) (fun i => (x i).val) =
        t₀.value + t₁.value + t₂.value := by
    simp [cubeForm, Fin.sum_univ_succ, t, d, x, CanonicalData.value]
    ring
  have hx : x ∈ rootTriples d M a X := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_, ?_⟩
    · intro i
      exact (t i).x_pos
    · rw [hform]
      exact hX
    · rw [hform, ← hmod]
      exact (ZMod.natCast_mod _ M).symm
  unfold representedWithParts
  apply mem_biUnion.mpr
  refine ⟨d, hd, ?_⟩
  apply mem_image.mpr
  exact ⟨x, hx, hform⟩

/-- The distinct values in a progression are no more numerous than the
ordered fixed-part representations. -/
theorem threeProgressionCount_le_fixedPartCount_sum (M a N : ℕ) :
    threeProgressionCount M a N ≤
      ∑ d ∈ partTriples (partsBelow N),
        fixedPartCount (fun i => (d i).val) M a N := by
  classical
  have hsub :
      (progressionBelow M a N).filter ThreePositiveCubeFullSum ⊆
        representedWithParts (partsBelow N) M a N := by
    intro n hn
    obtain ⟨hnP, hnthree⟩ := mem_filter.mp hn
    obtain ⟨hnrange, hnmod⟩ := mem_filter.mp hnP
    obtain ⟨t₀, t₁, t₂, heq⟩ := threePositive_has_canonical_data hnthree
    rw [heq] at hnrange hnmod
    rw [heq]
    apply represented_of_canonical_data t₀ t₁ t₂ M a N
    · exact Nat.le_of_lt (mem_range.mp hnrange)
    · simpa only [← heq] using hnmod
  calc
    threeProgressionCount M a N =
        ((progressionBelow M a N).filter ThreePositiveCubeFullSum).card := rfl
    _ ≤ (representedWithParts (partsBelow N) M a N).card := card_le_card hsub
    _ ≤ ∑ d ∈ partTriples (partsBelow N),
          fixedPartCount (fun i => (d i).val) M a N :=
        representedWithParts_card_le _ _ _ _

/-- The untruncated part of the ordered representation count. The part box
keeps this a finite sum for every `N`. -/
noncomputable def sieveTailCount (E : Finset CanonicalParts)
    (M a N : ℕ) : ℕ :=
  ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
    fixedPartCount (fun i => (d i).val) M a N

/-- The finite sieve bound to which the local and tail estimates may be
applied. No asymptotic estimate is used here. -/
theorem threeProgressionCount_le_sieve (D E : Finset CanonicalParts)
    (hDE : D ⊆ E) (M a N : ℕ) :
    threeProgressionCount M a N ≤
      (∑ d ∈ partTriples D,
        fixedPartCount (fun i => (d i).val) M a N) +
      (∑ d ∈ partTriples E \ partTriples D,
        fixedPartCount (fun i => (d i).val) M a N) +
      sieveTailCount E M a N := by
  classical
  let f : (Fin 3 → CanonicalParts) → ℕ :=
    fun d => fixedPartCount (fun i => (d i).val) M a N
  have hcore :
      (∑ d ∈ partTriples (partsBelow N) ∩ partTriples D, f d) ≤
        ∑ d ∈ partTriples D, f d := by
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => Nat.zero_le _)
  have hmiddle :
      (∑ d ∈ partTriples (partsBelow N) ∩
        (partTriples E \ partTriples D), f d) ≤
        ∑ d ∈ partTriples E \ partTriples D, f d := by
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => Nat.zero_le _)
  have hsplit := fixedPartCount_split D E hDE M a N
  have hfirst := threeProgressionCount_le_fixedPartCount_sum M a N
  dsimp [f, sieveTailCount] at *
  omega

/-- The largest root whose `d`-weighted cube can fit below `N`. -/
noncomputable def rootLimit (d N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun x => d * x ^ 3 ≤ N) N

private theorem rootLimit_spec (d N : ℕ) : d * (rootLimit d N) ^ 3 ≤ N := by
  classical
  unfold rootLimit
  exact Nat.findGreatest_spec (P := fun x => d * x ^ 3 ≤ N)
    (m := 0) (Nat.zero_le N) (by norm_num)

private theorem rootLimit_le (d N x : ℕ)
    (hxN : x ≤ N) (hx : d * x ^ 3 ≤ N) : x ≤ rootLimit d N := by
  classical
  unfold rootLimit
  exact Nat.le_findGreatest hxN hx

/-- Roots allowed in one coordinate before imposing the sum or congruence. -/
noncomputable def rootChoices (d N : ℕ) : Finset (Fin (N + 1)) := by
  classical
  exact univ.filter fun x => 0 < x.val ∧ d * x.val ^ 3 ≤ N

theorem rootChoices_card_le (d N : ℕ) :
    (rootChoices d N).card ≤ rootLimit d N := by
  classical
  let S := rootChoices d N
  have hsub : S.image Fin.val ⊆ Icc 1 (rootLimit d N) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    obtain ⟨_, hpos, hcube⟩ := mem_filter.mp hy
    exact mem_Icc.mpr ⟨hpos, rootLimit_le d N y.val
      (Nat.lt_succ_iff.mp y.isLt) hcube⟩
  calc
    S.card = (S.image Fin.val).card :=
      (card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Icc 1 (rootLimit d N)).card := card_le_card hsub
    _ = rootLimit d N := by simp

/-- A fixed-part representation count is bounded by the product of three
one-coordinate root limits. -/
theorem fixedPartCount_le_rootLimits (d : Fin 3 → CanonicalParts)
    (M a N : ℕ) :
    fixedPartCount (fun i => (d i).val) M a N ≤
      ∏ i : Fin 3, rootLimit (d i).val N := by
  classical
  let B : Finset (Fin 3 → Fin (N + 1)) :=
    Fintype.piFinset (fun i => rootChoices (d i).val N)
  have hsub : rootTriples d M a N ⊆ B := by
    intro x hx
    obtain ⟨_, hpos, hsum, _⟩ := mem_filter.mp hx
    apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_filter.mpr
    refine ⟨mem_univ _, hpos i, ?_⟩
    have hterm : (d i).val * (x i).val ^ 3 ≤
        cubeForm (fun j => (d j).val) (fun j => (x j).val) := by
      unfold cubeForm
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin 3 => (d j).val * (x j).val ^ 3)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hterm.trans hsum
  calc
    fixedPartCount (fun i => (d i).val) M a N =
        (rootTriples d M a N).card := (rootTriples_card d M a N).symm
    _ ≤ B.card := card_le_card hsub
    _ = ∏ i : Fin 3, (rootChoices (d i).val N).card := by
      simp [B, Fintype.card_piFinset]
    _ ≤ ∏ i : Fin 3, rootLimit (d i).val N := by
      exact Finset.prod_le_prod (fun i _ => rootChoices_card_le (d i).val N)

/-- A finite, exact tail estimate before replacing root limits by their
real cube-root weights. -/
theorem sieveTailCount_le_rootLimits (E : Finset CanonicalParts)
    (M a N : ℕ) :
    sieveTailCount E M a N ≤
      ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
        ∏ i : Fin 3, rootLimit (d i).val N := by
  classical
  unfold sieveTailCount
  exact Finset.sum_le_sum fun d _ => fixedPartCount_le_rootLimits d M a N

/-- The root limit has the expected real cube-root bound. -/
theorem rootLimit_le_realCubeRoot {d N : ℕ} (hd : 0 < d) :
    (rootLimit d N : ℝ) ≤ ((N : ℝ) / (d : ℝ)) ^ (1 / 3 : ℝ) := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hspec : (d : ℝ) * (rootLimit d N : ℝ) ^ 3 ≤ (N : ℝ) := by
    exact_mod_cast rootLimit_spec d N
  have hdiv : (rootLimit d N : ℝ) ^ (3 : ℝ) ≤
      (N : ℝ) / (d : ℝ) := by
    exact (le_div_iff₀ hdreal).mpr
      (by simpa [Real.rpow_natCast, mul_comm] using hspec)
  have hroot := (Real.le_rpow_inv_iff_of_pos
    (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) hdreal.le)
    (by norm_num : (0 : ℝ) < 3)).mpr hdiv
  simpa only [inv_eq_one_div] using hroot

/-- A real finite tail bound, before the algebraic rewrite into the paper's
`N (W³ - W_E³)`. -/
theorem sieveTailCount_le_realCubeRootSum (E : Finset CanonicalParts)
    (M a N : ℕ) :
    (sieveTailCount E M a N : ℝ) ≤
      ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
        ∏ i : Fin 3, ((N : ℝ) / ((d i).val : ℝ)) ^ (1 / 3 : ℝ) := by
  have hnat := sieveTailCount_le_rootLimits E M a N
  have hcast : (sieveTailCount E M a N : ℝ) ≤
      ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
        ∏ i : Fin 3, (rootLimit (d i).val N : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (Finset.sum_le_sum fun d _ =>
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
      (fun i _ => rootLimit_le_realCubeRoot (d i).property.pos))

/-- Weight assigned to one canonical 4-full part. -/
noncomputable def partWeight (d : CanonicalParts) : ℝ :=
  (d.val : ℝ) ^ (-(1 / 3 : ℝ))

private theorem cubeRootTriple_eq_weight (d : Fin 3 → CanonicalParts) (N : ℕ) :
    (∏ i : Fin 3, ((N : ℝ) / ((d i).val : ℝ)) ^ (1 / 3 : ℝ)) =
      (N : ℝ) * ∏ i : Fin 3, partWeight (d i) := by
  let u : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
  have hu : u ^ 3 = (N : ℝ) := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N) (1 / 3 : ℝ) 3]
    norm_num
  have hfactor (i : Fin 3) :
      ((N : ℝ) / ((d i).val : ℝ)) ^ (1 / 3 : ℝ) =
        u * partWeight (d i) := by
    calc
      ((N : ℝ) / ((d i).val : ℝ)) ^ (1 / 3 : ℝ) =
          (N : ℝ) ^ (1 / 3 : ℝ) /
            ((d i).val : ℝ) ^ (1 / 3 : ℝ) :=
        Real.div_rpow (Nat.cast_nonneg N) (Nat.cast_nonneg _) _
      _ = (N : ℝ) ^ (1 / 3 : ℝ) *
            ((d i).val : ℝ) ^ (-(1 / 3 : ℝ)) := by
        exact (congrArg ((N : ℝ) ^ (1 / 3 : ℝ) * ·)
          (Real.rpow_neg (Nat.cast_nonneg _) (1 / 3 : ℝ)).symm)
      _ = u * partWeight (d i) := rfl
  simp only [Fin.prod_univ_three, hfactor]
  rw [← hu]
  ring

/-- The omitted ordered representations are bounded by the source's
cube-root weights, with only a finite sum on the right. -/
theorem sieveTailCount_le_finiteWeights (E : Finset CanonicalParts)
    (M a N : ℕ) :
    (sieveTailCount E M a N : ℝ) ≤
      (N : ℝ) *
        ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
          ∏ i : Fin 3, partWeight (d i) := by
  calc
    (sieveTailCount E M a N : ℝ) ≤
        ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
          ∏ i : Fin 3, ((N : ℝ) / ((d i).val : ℝ)) ^ (1 / 3 : ℝ) :=
      sieveTailCount_le_realCubeRootSum E M a N
    _ = (N : ℝ) *
        ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
          ∏ i : Fin 3, partWeight (d i) := by
      simp_rw [cubeRootTriple_eq_weight]
      rw [Finset.mul_sum]

private theorem partWeight_nonneg (d : CanonicalParts) : 0 ≤ partWeight d := by
  unfold partWeight
  positivity

private theorem partTriples_inter (B E : Finset CanonicalParts) :
    partTriples (B ∩ E) = partTriples B ∩ partTriples E := by
  classical
  ext d
  simp [mem_partTriples, forall_and]

private theorem sum_partTriple_weights (B : Finset CanonicalParts) :
    (∑ d ∈ partTriples B, ∏ i : Fin 3, partWeight (d i)) =
      (∑ d ∈ B, partWeight d) ^ 3 := by
  classical
  simpa only [partTriples] using
    (Finset.sum_pow' B partWeight 3).symm

/-- The omitted triple weight is exactly a difference of finite cubes. -/
theorem finiteTailWeight_eq_cubeDiff (B E : Finset CanonicalParts) :
    (∑ d ∈ partTriples B \ partTriples E,
      ∏ i : Fin 3, partWeight (d i)) =
      (∑ d ∈ B, partWeight d) ^ 3 -
        (∑ d ∈ B ∩ E, partWeight d) ^ 3 := by
  classical
  let f : (Fin 3 → CanonicalParts) → ℝ :=
    fun d => ∏ i : Fin 3, partWeight (d i)
  have hsplit := Finset.sum_inter_add_sum_sdiff
    (partTriples B) (partTriples E) f
  rw [← partTriples_inter] at hsplit
  rw [sum_partTriple_weights, sum_partTriple_weights] at hsplit
  dsimp [f] at hsplit
  linarith

/-- A finite tail is at most three times the square of the total finite
weight times the omitted one-part weight. -/
theorem finiteTailWeight_le_three (B E : Finset CanonicalParts) :
    (∑ d ∈ partTriples B \ partTriples E,
      ∏ i : Fin 3, partWeight (d i)) ≤
      3 * (∑ d ∈ B, partWeight d) ^ 2 *
        (∑ d ∈ B \ E, partWeight d) := by
  let U : ℝ := ∑ d ∈ B, partWeight d
  let V : ℝ := ∑ d ∈ B ∩ E, partWeight d
  let T : ℝ := ∑ d ∈ B \ E, partWeight d
  have hUV : U = V + T := by
    simpa only [U, V, T, add_comm] using
      (Finset.sum_inter_add_sum_sdiff B E partWeight).symm
  have hV : 0 ≤ V := Finset.sum_nonneg fun d _ => partWeight_nonneg d
  have hT : 0 ≤ T := Finset.sum_nonneg fun d _ => partWeight_nonneg d
  have hVU : V ≤ U := by linarith
  have hU : 0 ≤ U := by linarith
  have hsq : V ^ 2 ≤ U ^ 2 := by nlinarith
  have hcross : U * V ≤ U ^ 2 := by nlinarith
  have hpoly : U ^ 2 + U * V + V ^ 2 ≤ 3 * U ^ 2 := by nlinarith
  rw [finiteTailWeight_eq_cubeDiff]
  change U ^ 3 - V ^ 3 ≤ 3 * U ^ 2 * T
  calc
    U ^ 3 - V ^ 3 = (U - V) * (U ^ 2 + U * V + V ^ 2) := by ring
    _ ≤ (U - V) * (3 * U ^ 2) :=
      mul_le_mul_of_nonneg_left hpoly (sub_nonneg.mpr hVU)
    _ = 3 * U ^ 2 * T := by rw [show U - V = T by linarith]; ring

/-- Elementary finite form of the paper's tail bound (15). -/
theorem sieveTailCount_le_threeFiniteWeights (E : Finset CanonicalParts)
    (M a N : ℕ) :
    (sieveTailCount E M a N : ℝ) ≤
      3 * (N : ℝ) *
        (∑ d ∈ partsBelow N, partWeight d) ^ 2 *
        (∑ d ∈ partsBelow N \ E, partWeight d) := by
  calc
    (sieveTailCount E M a N : ℝ) ≤
        (N : ℝ) *
          ∑ d ∈ partTriples (partsBelow N) \ partTriples E,
            ∏ i : Fin 3, partWeight (d i) :=
      sieveTailCount_le_finiteWeights E M a N
    _ ≤ (N : ℝ) *
        (3 * (∑ d ∈ partsBelow N, partWeight d) ^ 2 *
          (∑ d ∈ partsBelow N \ E, partWeight d)) :=
      mul_le_mul_of_nonneg_left
        (finiteTailWeight_le_three (partsBelow N) E) (Nat.cast_nonneg N)
    _ = 3 * (N : ℝ) *
        (∑ d ∈ partsBelow N, partWeight d) ^ 2 *
        (∑ d ∈ partsBelow N \ E, partWeight d) := by ring

/-- The convergent total weight `W` in Section 2. -/
noncomputable def totalPartWeight : ℝ := ∑' d : CanonicalParts, partWeight d

/-- The weight omitted by a finite truncation, expressed as an indicator sum. -/
noncomputable def tailPartWeight (E : Finset CanonicalParts) : ℝ :=
  ∑' d : CanonicalParts, if d ∉ E then partWeight d else 0

private theorem summable_partWeight : Summable partWeight := by
  exact summable_canonicalPart_weight

private theorem summable_tailPartWeight (E : Finset CanonicalParts) :
    Summable (fun d : CanonicalParts => if d ∉ E then partWeight d else 0) := by
  apply Summable.of_nonneg_of_le
    (fun d => by split_ifs <;> simp [partWeight_nonneg])
    (fun d => by split_ifs <;> simp [partWeight_nonneg d])
    summable_partWeight

private theorem finiteWeight_le_total (B : Finset CanonicalParts) :
    (∑ d ∈ B, partWeight d) ≤ totalPartWeight :=
  summable_partWeight.sum_le_tsum B (fun d _ => partWeight_nonneg d)

private theorem finiteTailWeight_le_totalTail (B E : Finset CanonicalParts) :
    (∑ d ∈ B \ E, partWeight d) ≤ tailPartWeight E := by
  have heq : (∑ d ∈ B \ E, partWeight d) =
      ∑ d ∈ B, (if d ∉ E then partWeight d else 0) := by
    classical
    rw [Finset.sdiff_eq_filter, Finset.sum_ite]
    simp
  rw [heq]
  exact (summable_tailPartWeight E).sum_le_tsum B
    (fun d _ => by split_ifs <;> simp [partWeight_nonneg])

/-- Any positive error budget can be met by a finite set of canonical parts. -/
theorem exists_tailPartWeight_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset CanonicalParts, tailPartWeight E < ε := by
  have htend := tendsto_tsum_compl_atTop_zero partWeight
  obtain ⟨E, hE⟩ := ((tendsto_order.1 htend).2 ε hε).exists
  refine ⟨E, ?_⟩
  have heq : tailPartWeight E =
      ∑' d : {d : CanonicalParts // d ∉ E}, partWeight d.val := by
    classical
    unfold tailPartWeight
    calc
      (∑' d : CanonicalParts, if d ∉ E then partWeight d else 0) =
          ∑' d : CanonicalParts,
            (Set.indicator {d : CanonicalParts | d ∉ E} partWeight d) := by
        congr 1
        funext d
        simp [Set.indicator_apply]
      _ = ∑' d : {d : CanonicalParts // d ∉ E}, partWeight d.val :=
        (_root_.tsum_subtype {d : CanonicalParts | d ∉ E} partWeight).symm
  rwa [heq]

/-- The truncation tail is uniformly bounded by the convergent one-part
weight series. This is the real inequality used in (15), with an equivalent
three-times-tail form convenient for choosing `E`. -/
theorem sieveTailCount_le_globalWeights (E : Finset CanonicalParts)
    (M a N : ℕ) :
    (sieveTailCount E M a N : ℝ) ≤
      3 * (N : ℝ) * totalPartWeight ^ 2 * tailPartWeight E := by
  let B := partsBelow N
  let U : ℝ := ∑ d ∈ B, partWeight d
  let T : ℝ := ∑ d ∈ B \ E, partWeight d
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun d _ => partWeight_nonneg d
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun d _ => partWeight_nonneg d
  have hU : U ≤ totalPartWeight := finiteWeight_le_total B
  have hT : T ≤ tailPartWeight E := finiteTailWeight_le_totalTail B E
  have hW0 : 0 ≤ totalPartWeight := hU0.trans hU
  have hTail0 : 0 ≤ tailPartWeight E := hT0.trans hT
  have hsq : U ^ 2 ≤ totalPartWeight ^ 2 := by nlinarith
  have hprod : U ^ 2 * T ≤ totalPartWeight ^ 2 * tailPartWeight E := by
    exact (mul_le_mul_of_nonneg_right hsq hT0).trans
      (mul_le_mul_of_nonneg_left hT (sq_nonneg _))
  have hfirst := sieveTailCount_le_threeFiniteWeights E M a N
  dsimp [B, U, T] at *
  nlinarith [mul_nonneg (by positivity : 0 ≤ 3 * (N : ℝ))
    (sub_nonneg.mpr hprod)]

end Erdos940
