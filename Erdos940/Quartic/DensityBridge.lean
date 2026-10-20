import Erdos940.Quartic.FixedParts
import Erdos940.Quartic.Bridge
import Erdos940.Progression
import Mathlib.Data.Fintype.Pi

/-!
# The counting bridge for four fourth-powerful summands

The elementary final stage of the quartic complement argument. Distinct
represented values in a residue class are bounded by the ordered first moment
over canonical coefficient quadruples. A sufficiently small first moment,
together with the sparse short-sum estimate, yields positive lower density of
the complement. Arithmetic bounds on the first moment remain explicit inputs.
-/

namespace Erdos940.Quartic

open Finset

/-- Canonical coefficients no larger than `X`. -/
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

/-- Ordered quadruples of coefficients in a finite family. -/
noncomputable def partQuadruples (D : Finset CanonicalParts) :
    Finset (Fin 4 → CanonicalParts) := by
  classical
  exact Fintype.piFinset (fun _ : Fin 4 => D)

theorem mem_partQuadruples {D : Finset CanonicalParts}
    {d : Fin 4 → CanonicalParts} :
    d ∈ partQuadruples D ↔ ∀ i, d i ∈ D := by
  classical
  simp [partQuadruples, Fintype.mem_piFinset]

/-- Positive root quadruples counted with fixed coefficients. -/
noncomputable def rootQuadruples (d : Fin 4 → CanonicalParts) (M a X : ℕ) :
    Finset (Fin 4 → Fin (X + 1)) := by
  classical
  exact univ.filter fun x =>
    (∀ i, 0 < (x i).val) ∧
      quarticForm (fun i => (d i).val) (fun i => (x i).val) ≤ X ∧
      (quarticForm (fun i => (d i).val) (fun i => (x i).val) : ZMod M) =
        (a : ZMod M)

theorem rootQuadruples_card (d : Fin 4 → CanonicalParts) (M a X : ℕ) :
    (rootQuadruples d M a X).card =
      fixedPartCount (fun i => (d i).val) M a X := by
  classical
  simp [rootQuadruples, fixedPartCount, Fintype.card_subtype]

/-- Values represented using coefficients in a finite family. -/
noncomputable def representedWithParts (D : Finset CanonicalParts)
    (M a X : ℕ) : Finset ℕ := by
  classical
  exact (partQuadruples D).biUnion fun d =>
    (rootQuadruples d M a X).image
      (fun x => quarticForm (fun i => (d i).val) (fun i => (x i).val))

theorem representedWithParts_card_le (D : Finset CanonicalParts)
    (M a X : ℕ) :
    (representedWithParts D M a X).card ≤
      ∑ d ∈ partQuadruples D,
        fixedPartCount (fun i => (d i).val) M a X := by
  classical
  unfold representedWithParts
  calc
    ((partQuadruples D).biUnion fun d =>
        (rootQuadruples d M a X).image
          (fun x => quarticForm (fun i => (d i).val) (fun i => (x i).val))).card
      ≤ ∑ d ∈ partQuadruples D,
          ((rootQuadruples d M a X).image
            (fun x => quarticForm (fun i => (d i).val) (fun i => (x i).val))).card :=
        card_biUnion_le
    _ ≤ ∑ d ∈ partQuadruples D, (rootQuadruples d M a X).card :=
        sum_le_sum fun _ _ => card_image_le
    _ = ∑ d ∈ partQuadruples D,
          fixedPartCount (fun i => (d i).val) M a X := by
        apply sum_congr rfl
        intro d _
        exact rootQuadruples_card d M a X

theorem canonicalData_factor_bounds (t : CanonicalData) :
    t.x ≤ t.value ∧ t.b ^ 5 * t.c ^ 6 * t.d ^ 7 ≤ t.value := by
  have hx : 1 ≤ t.x ^ 4 := pow_pos t.x_pos _
  have hp : 1 ≤ t.b ^ 5 * t.c ^ 6 * t.d ^ 7 :=
    Nat.mul_pos (Nat.mul_pos (pow_pos t.b_pos _) (pow_pos t.c_pos _))
      (pow_pos t.d_pos _)
  constructor
  · calc
      t.x ≤ t.x ^ 4 := le_self_pow₀ t.x_pos (by decide)
      _ ≤ t.x ^ 4 * (t.b ^ 5 * t.c ^ 6 * t.d ^ 7) :=
        le_mul_of_one_le_right (Nat.zero_le _) hp
      _ = t.value := by simp [CanonicalData.value]; ring
  · calc
      t.b ^ 5 * t.c ^ 6 * t.d ^ 7 ≤
          t.x ^ 4 * (t.b ^ 5 * t.c ^ 6 * t.d ^ 7) :=
        le_mul_of_one_le_left (Nat.zero_le _) hx
      _ = t.value := by simp [CanonicalData.value]; ring

/-- Four positive summands have ordered canonical data. -/
theorem fourPositive_has_canonical_data {n : ℕ} (hn : FourPositiveSum n) :
    ∃ t₀ t₁ t₂ t₃ : CanonicalData,
      n = t₀.value + t₁.value + t₂.value + t₃.value := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := hn
  obtain ⟨t₀, rfl⟩ := exists_canonicalData_of_fourFull a ha
  obtain ⟨t₁, rfl⟩ := exists_canonicalData_of_fourFull b hb
  obtain ⟨t₂, rfl⟩ := exists_canonicalData_of_fourFull c hc
  obtain ⟨t₃, rfl⟩ := exists_canonicalData_of_fourFull d hd
  exact ⟨t₀, t₁, t₂, t₃, rfl⟩

private theorem represented_of_canonical_data
    (t₀ t₁ t₂ t₃ : CanonicalData) (M a X : ℕ)
    (hX : t₀.value + t₁.value + t₂.value + t₃.value ≤ X)
    (hmod : (t₀.value + t₁.value + t₂.value + t₃.value) % M = a) :
    t₀.value + t₁.value + t₂.value + t₃.value ∈
      representedWithParts (partsBelow X) M a X := by
  classical
  let t : Fin 4 → CanonicalData := ![t₀, t₁, t₂, t₃]
  let d : Fin 4 → CanonicalParts :=
    fun i => ⟨(t i).b ^ 5 * (t i).c ^ 6 * (t i).d ^ 7, (t i).part⟩
  have hterm (i : Fin 4) : (t i).value ≤ X := by
    fin_cases i <;> dsimp [t] <;> omega
  have hd : d ∈ partQuadruples (partsBelow X) := by
    apply mem_partQuadruples.mpr
    intro i
    apply mem_partsBelow.mpr
    exact (canonicalData_factor_bounds (t i)).2.trans (hterm i)
  let x : Fin 4 → Fin (X + 1) :=
    fun i => ⟨(t i).x, Nat.lt_succ_of_le
      ((canonicalData_factor_bounds (t i)).1.trans (hterm i))⟩
  have hform :
      quarticForm (fun i => (d i).val) (fun i => (x i).val) =
        t₀.value + t₁.value + t₂.value + t₃.value := by
    simp [quarticForm, Fin.sum_univ_succ, t, d, x, CanonicalData.value]
    ring
  have hx : x ∈ rootQuadruples d M a X := by
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

/-- Exactly four positive summands, restricted to one residue class. -/
noncomputable def fourProgressionCount (M a N : ℕ) : ℕ := by
  classical
  exact ((progressionBelow M a N).filter FourPositiveSum).card

/-- Distinct represented values are no more numerous than ordered
fixed-coefficient representations. -/
theorem fourProgressionCount_le_fixedPartCount_sum (M a N : ℕ) :
    fourProgressionCount M a N ≤
      ∑ d ∈ partQuadruples (partsBelow N),
        fixedPartCount (fun i => (d i).val) M a N := by
  classical
  have hsub :
      (progressionBelow M a N).filter FourPositiveSum ⊆
        representedWithParts (partsBelow N) M a N := by
    intro n hn
    obtain ⟨hnP, hnFour⟩ := mem_filter.mp hn
    obtain ⟨hnRange, hnMod⟩ := mem_filter.mp hnP
    obtain ⟨t₀, t₁, t₂, t₃, heq⟩ := fourPositive_has_canonical_data hnFour
    rw [heq] at hnRange hnMod
    rw [heq]
    apply represented_of_canonical_data t₀ t₁ t₂ t₃ M a N
    · exact Nat.le_of_lt (mem_range.mp hnRange)
    · simpa only [← heq] using hnMod
  calc
    fourProgressionCount M a N =
        ((progressionBelow M a N).filter FourPositiveSum).card := rfl
    _ ≤ (representedWithParts (partsBelow N) M a N).card := card_le_card hsub
    _ ≤ ∑ d ∈ partQuadruples (partsBelow N),
          fixedPartCount (fun i => (d i).val) M a N :=
        representedWithParts_card_le _ _ _ _

/-- Every residue-class value is missing, has four positive summands, or
belongs to the sparse short-sum set. -/
theorem progression_le_missing_add_counts (M a N : ℕ) :
    progressionCount M a N ≤
      missingCount 4 N + fourProgressionCount M a N + atMostThreeCount N := by
  classical
  let P := progressionBelow M a N
  let A := (Finset.range N).filter fun n => ¬ Representable 4 n
  let B := P.filter FourPositiveSum
  let C := (Finset.range N).filter AtMostThreeFullSum
  have hcover : P ⊆ A ∪ (B ∪ C) := by
    intro n hn
    have hnN : n ∈ Finset.range N := (mem_filter.mp hn).1
    by_cases hr : Representable 4 n
    · rcases (representable_four_iff n).mp hr with hfour | hthree
      · exact mem_union.mpr (Or.inr
          (mem_union.mpr (Or.inl (mem_filter.mpr ⟨hn, hfour⟩))))
      · exact mem_union.mpr (Or.inr
          (mem_union.mpr (Or.inr (mem_filter.mpr ⟨hnN, hthree⟩))))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hnN, hr⟩))
  have hcount : P.card ≤ A.card + B.card + C.card := by
    calc
      P.card ≤ (A ∪ (B ∪ C)).card := card_le_card hcover
      _ ≤ A.card + (B ∪ C).card := card_union_le _ _
      _ ≤ A.card + (B.card + C.card) :=
        Nat.add_le_add_left (card_union_le B C) A.card
      _ = A.card + B.card + C.card := by omega
  simpa only [P, A, B, C, progressionCount, fourProgressionCount,
    missingCount, atMostThreeCount] using hcount

/-- A quantitative small first-moment bound implies positive lower density
of the complement. The arithmetic estimate is an explicit hypothesis. -/
theorem positiveLowerDensity_of_firstMoment_bound {M a : ℕ}
    (hM : 0 < M) (ha : a < M)
    (hmoment : ∀ᶠ N in Filter.atTop,
      8 * M * (∑ d ∈ partQuadruples (partsBelow N),
        fixedPartCount (fun i => (d i).val) M a N) ≤ N) :
    HasPositiveLowerDensityComplementFor 4 := by
  have hshort : ∀ᶠ N in Filter.atTop,
      8 * M * atMostThreeCount N ≤ N :=
    atMostThreeCount_eventually_small (8 * M)
  have hlarge := eventually_progressionCount_lower hM ha
  refine ⟨8 * M, by positivity, ?_⟩
  filter_upwards [hmoment, hshort, hlarge] with N hmomentN hshortN hclass
  have hpositive := fourProgressionCount_le_fixedPartCount_sum M a N
  have hcover := progression_le_missing_add_counts M a N
  have hscaled :
      8 * M * progressionCount M a N ≤
        8 * M * missingCount 4 N +
        8 * M * fourProgressionCount M a N +
        8 * M * atMostThreeCount N := by
    nlinarith
  nlinarith

/-- The finite canonical-coefficient box contributes no more than the
nonnegative global first moment. -/
theorem finiteFirstMoment_le_global (M a N : ℕ) (hN : 0 < N) :
    ((∑ d ∈ partQuadruples (partsBelow N),
      fixedPartCount (fun i => (d i).val) M a N : ℕ) : ℝ) / (N : ℝ) ≤
      ∑' d : Fin 4 → CanonicalParts,
        (fixedPartCount (fun i => (d i).val) M a N : ℝ) / (N : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable (fun d : Fin 4 → CanonicalParts =>
      (fixedPartCount (fun i => (d i).val) M a N : ℝ) / (N : ℝ)) := by
    apply Summable.of_nonneg_of_le
      (fun _ => div_nonneg (Nat.cast_nonneg _) hNreal.le)
      (fun d => ?_) summable_coefficientWeight
    have hbound := fixedPartCount_le_weight (fun i => (d i).val)
      (fun i => (d i).property.pos) M a N
    apply (div_le_iff₀ hNreal).2
    simpa only [coefficientWeight, mul_comm] using hbound
  have hle := hsum.sum_le_tsum (partQuadruples (partsBelow N))
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) hNreal.le)
  simpa only [Nat.cast_sum, Finset.sum_div] using hle

/-- A strict bound on the global asymptotic first moment is the only
arithmetic input needed by the elementary density argument. -/
theorem positiveLowerDensity_of_firstMoment_limit {M a : ℕ} [NeZero M]
    (hM : 0 < M) (ha : a < M)
    (hsmall :
      (∑' d : Fin 4 → CanonicalParts,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) <
        1 / (8 * (M : ℝ))) :
    HasPositiveLowerDensityComplementFor 4 := by
  have hratio : ∀ᶠ N in Filter.atTop,
      (∑' d : Fin 4 → CanonicalParts,
        (fixedPartCount (fun i => (d i).val) M a N : ℝ) / (N : ℝ)) <
          1 / (8 * (M : ℝ)) :=
    (firstMoment_asymptotic M a).eventually_lt_const hsmall
  have hN : ∀ᶠ N : ℕ in Filter.atTop, 0 < N :=
    Filter.eventually_gt_atTop 0
  have hmoment : ∀ᶠ N in Filter.atTop,
      8 * M * (∑ d ∈ partQuadruples (partsBelow N),
        fixedPartCount (fun i => (d i).val) M a N) ≤ N := by
    filter_upwards [hratio, hN] with N hratioN hNpos
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have hscale : (0 : ℝ) < 8 * (M : ℝ) := by positivity
    have hfinite := finiteFirstMoment_le_global M a N hNpos
    have hfinite' :
        ((∑ d ∈ partQuadruples (partsBelow N),
          fixedPartCount (fun i => (d i).val) M a N : ℕ) : ℝ) / (N : ℝ) <
          1 / (8 * (M : ℝ)) := lt_of_le_of_lt hfinite hratioN
    have hreal : (8 : ℝ) * (M : ℝ) *
        ((∑ d ∈ partQuadruples (partsBelow N),
          fixedPartCount (fun i => (d i).val) M a N : ℕ) : ℝ) ≤ N := by
      have h := (div_lt_div_iff₀ hNreal hscale).mp hfinite'
      nlinarith
    exact_mod_cast hreal
  exact positiveLowerDensity_of_firstMoment_bound hM ha hmoment

/-- The corresponding coinfinitude conclusion. -/
theorem coinfinite_of_firstMoment_limit {M a : ℕ} [NeZero M]
    (hM : 0 < M) (ha : a < M)
    (hsmall :
      (∑' d : Fin 4 → CanonicalParts,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) <
        1 / (8 * (M : ℝ))) :
    CoinfiniteFor 4 :=
  coinfiniteFor_of_positiveLowerDensity
    (positiveLowerDensity_of_firstMoment_limit hM ha hsmall)

end Erdos940.Quartic
