module

public import Erdos940.Cubic.Progression
public import Erdos940.Cubic.SmallSums
public import Erdos940.Cubic.Sieve
public import Erdos940.Cubic.ParameterSelection
public import Erdos940.Cubic.LocalProducts
public import Erdos940.Cubic.WeightedAggregation

/-!
# Assembly of the r = 3 infinitude proof

The coinfinitude theorem for `r = 3` combines a small count of sums of exactly
three positive cube-full numbers in a suitable progression with a sublinear
count of values representable by at most two summands. It does not establish
the density-zero statement.
-/

@[expose] public section

namespace Erdos940

/-- A quantitative instance of the paper's progression theorem, with enough
slack to absorb the sparse one- and two-term sums. -/
def HasSparseThreeSumProgression : Prop :=
  ∃ M a : ℕ, 0 < M ∧ a < M ∧
    ∀ᶠ N in Filter.atTop,
      8 * M * threeProgressionCount M a N ≤ N

/-- The three quantitative bounds needed after choosing the modulus and
the nested finite part families. The factor `32` leaves room when adding the
three contributions and comparing with the progression size. -/
def HasSieveEstimates : Prop :=
  ∃ (M a : ℕ) (D E : Finset CanonicalParts),
    0 < M ∧ a < M ∧ D ⊆ E ∧
    (∀ᶠ N in Filter.atTop,
      32 * M * (∑ d ∈ partTriples D,
        fixedPartCount (fun i => (d i).val) M a N) ≤ N) ∧
    (∀ᶠ N in Filter.atTop,
      32 * M * (∑ d ∈ partTriples E \ partTriples D,
        fixedPartCount (fun i => (d i).val) M a N) ≤ N) ∧
    (∀ᶠ N in Filter.atTop,
      32 * M * sieveTailCount E M a N ≤ N)

/-- Convert a strict upper bound on an asymptotic counting ratio into the
eventual integer inequality used by the sieve. -/
theorem eventually_scaled_count_le_of_limit
    (f : ℕ → ℕ) (M : ℕ) (hM : 0 < M) (c : ℝ)
    (hlimit : Filter.Tendsto (fun N : ℕ => (f N : ℝ) / (N : ℝ))
      Filter.atTop (nhds c))
    (hc : c < 1 / (32 * (M : ℝ))) :
    ∀ᶠ N in Filter.atTop, 32 * M * f N ≤ N := by
  have hratio : ∀ᶠ N in Filter.atTop,
      (f N : ℝ) / (N : ℝ) < 1 / (32 * (M : ℝ)) :=
    hlimit.eventually_lt_const hc
  have hN : ∀ᶠ N : ℕ in Filter.atTop, 0 < N :=
    Filter.eventually_gt_atTop 0
  filter_upwards [hratio, hN] with N hratioN hNpos
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hMscale : (0 : ℝ) < 32 * (M : ℝ) := by positivity
  have hreal : (32 : ℝ) * (M : ℝ) * (f N : ℝ) ≤ (N : ℝ) := by
    have h := (div_lt_div_iff₀ hNreal hMscale).mp hratioN
    nlinarith
  exact_mod_cast hreal

/-- The fixed-part asymptotic can be summed over any finite collection of
ordered canonical part triples. -/
theorem finite_fixedPartCount_asymptotic
    (F : Finset (Fin 3 → CanonicalParts)) (M a : ℕ) [NeZero M] :
    Filter.Tendsto
      (fun N : ℕ =>
        ((∑ d ∈ F, fixedPartCount (fun i => (d i).val) M a N : ℕ) : ℝ) /
          (N : ℝ))
      Filter.atTop
      (nhds (∑ d ∈ F,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 3)) := by
  have hsum := tendsto_finsetSum F (fun d _ =>
    fixedPartCount_asymptotic (fun i => (d i).val)
      (fun i => (d i).property.pos) M a)
  convert hsum using 1
  · funext N
    rw [Nat.cast_sum, Finset.sum_div]

/-- A sufficiently small global weight tail gives the third sieve estimate
uniformly in the cutoff. -/
theorem sieveTailCount_scaled_le
    (E : Finset CanonicalParts) (M a : ℕ)
    (hsmall : (32 * (M : ℝ)) *
      (3 * totalPartWeight ^ 2 * tailPartWeight E) ≤ 1) (N : ℕ) :
    32 * M * sieveTailCount E M a N ≤ N := by
  have htail := sieveTailCount_le_globalWeights E M a N
  have hscale : (0 : ℝ) ≤ 32 * (M : ℝ) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left htail hscale
  have hsecond := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg (α := ℝ) N)
  have hreal : (32 : ℝ) * (M : ℝ) * (sieveTailCount E M a N : ℝ) ≤ N := by
    nlinarith
  exact_mod_cast hreal

/-- Once the modulus and core part set are fixed, enlarge the parts so the
untruncated remainder satisfies the sieve budget at every cutoff. -/
theorem exists_parts_with_sieve_tail_estimate
    (D : Finset CanonicalParts) (M a : ℕ) :
    ∃ E : Finset CanonicalParts, D ⊆ E ∧
      ∀ N : ℕ, 32 * M * sieveTailCount E M a N ≤ N := by
  obtain ⟨E, hDE, hsmall⟩ :=
    exists_larger_parts_for_sieve_estimate D M
  exact ⟨E, hDE, fun N => sieveTailCount_scaled_le E M a hsmall.le N⟩

private theorem finitePartWeight_le_total (D : Finset CanonicalParts) :
    (∑ d ∈ D, partWeight d) ≤ totalPartWeight := by
  unfold totalPartWeight
  exact (show Summable partWeight by
    exact summable_canonicalPart_weight).sum_le_tsum D
      (fun d _ => by unfold partWeight; positivity)

private theorem totalPartWeight_nonneg : 0 ≤ totalPartWeight := by
  unfold totalPartWeight
  exact tsum_nonneg (fun d => by unfold partWeight; positivity)

private theorem weightedPartTail_nonneg (D : Finset CanonicalParts) :
    0 ≤ weightedPartTail D := by
  unfold weightedPartTail
  exact tsum_nonneg (fun d => by positivity)

/-- The finite core family contributes at most the cubic unweighted part sum
times the exponential saving supplied by the chosen primes. -/
theorem core_fixedPart_limit_le
    (D : Finset CanonicalParts) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, GoodPrime (partValues D) q)
    (a : ℕ) (ha : ∀ q ∈ Q, IsNoncubeMod q (a : ZMod q)) :
    (∑ d ∈ partTriples D,
      fixedPartVolume (fun i => (d i).val) *
        (@localCount (fun i => (d i).val) (goodModulus Q) a
          ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 3) ≤
      Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / q) *
        (∑ e ∈ D, partWeight e) ^ 3 / (goodModulus Q : ℝ) := by
  classical
  have hMpos : (0 : ℝ) < goodModulus Q := by
    exact_mod_cast goodModulus_pos hQ
  have hterm (d : Fin 3 → CanonicalParts) (hd : d ∈ partTriples D) :
      fixedPartVolume (fun i => (d i).val) *
        (@localCount (fun i => (d i).val) (goodModulus Q) a
          ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 3 ≤
        (∏ i, partWeight (d i)) *
          Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / q) /
          (goodModulus Q : ℝ) := by
    have hdpos : ∀ i, 0 < (d i).val := fun i => (d i).property.pos
    have hvol := fixedPartVolume_le_coeff_product
      (fun i => (d i).val) hdpos
    have hvol' : fixedPartVolume (fun i => (d i).val) ≤
        ∏ i, partWeight (d i) := by
      simpa [partWeight, show (-(3 : ℝ)⁻¹) = -(1 / 3 : ℝ) by norm_num]
        using hvol
    have hlocal := core_localDensity_product_le_exp hQ a ha
      (fun i => (d i).val) (fun i => by
        exact Finset.mem_image.mpr ⟨d i, (mem_partTriples.mp hd) i, rfl⟩)
    have hprod_nonneg : 0 ≤ ∏ q ∈ Q,
        localDensityFactor q (fun i => (d i).val) a :=
      Finset.prod_nonneg (fun q _ => localDensityFactor_nonneg q _ a)
    have hweight_nonneg : 0 ≤ ∏ i, partWeight (d i) :=
      Finset.prod_nonneg (fun i _ => by
        unfold partWeight
        exact Real.rpow_nonneg (by positivity) _)
    rw [mul_div_assoc, localCount_div_cube_eq_localDensity_product_div hQ]
    calc
      fixedPartVolume (fun i => (d i).val) *
          ((∏ q ∈ Q, localDensityFactor q (fun i => (d i).val) a) /
            (goodModulus Q : ℝ))
          ≤ (∏ i, partWeight (d i)) *
              ((∏ q ∈ Q, localDensityFactor q (fun i => (d i).val) a) /
                (goodModulus Q : ℝ)) := by
            gcongr
      _ ≤ (∏ i, partWeight (d i)) *
            (Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / q) /
              (goodModulus Q : ℝ)) := by
          gcongr
      _ = _ := by ring
  calc
    (∑ d ∈ partTriples D,
      fixedPartVolume (fun i => (d i).val) *
        (@localCount (fun i => (d i).val) (goodModulus Q) a
          ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 3)
        ≤ ∑ d ∈ partTriples D,
            (∏ i, partWeight (d i)) *
              Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / q) /
              (goodModulus Q : ℝ) := Finset.sum_le_sum hterm
    _ = Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / q) *
          (∑ e ∈ D, partWeight e) ^ 3 / (goodModulus Q : ℝ) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      rw [show (∑ d ∈ partTriples D, ∏ i, partWeight (d i)) =
        (∑ e ∈ D, partWeight e) ^ 3 by
          simpa [partTriples] using
            (Finset.sum_pow' D partWeight 3).symm]
      ring

/-- The finite middle family is controlled by the weighted part tail and
the uniform local bound. -/
theorem middle_fixedPart_limit_le
    (D E : Finset CanonicalParts) (hDE : D ⊆ E) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, GoodPrime (partValues D) q)
    (a : ℕ) (ha : ∀ q ∈ Q, IsNoncubeMod q (a : ZMod q)) :
    (∑ d ∈ partTriples E \ partTriples D,
      fixedPartVolume (fun i => (d i).val) *
        (@localCount (fun i => (d i).val) (goodModulus Q) a
          ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 3) ≤
      Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / q) *
        (3 * totalWeightedPartWeight ^ 2 * weightedPartTail D) /
          (goodModulus Q : ℝ) := by
  classical
  have hMpos : (0 : ℝ) < goodModulus Q := by
    exact_mod_cast goodModulus_pos hQ
  have hterm (d : Fin 3 → CanonicalParts)
      (_hd : d ∈ partTriples E \ partTriples D) :
      fixedPartVolume (fun i => (d i).val) *
        (@localCount (fun i => (d i).val) (goodModulus Q) a
          ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 3 ≤
        (∏ i, weightedPartWeight (d i)) *
          Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / q) /
          (goodModulus Q : ℝ) := by
    have hdpos : ∀ i, 0 < (d i).val := fun i => (d i).property.pos
    have hvol := fixedPartVolume_le_coeff_product
      (fun i => (d i).val) hdpos
    have hvol' : fixedPartVolume (fun i => (d i).val) ≤
        ∏ i, partWeight (d i) := by
      simpa [partWeight, show (-(3 : ℝ)⁻¹) = -(1 / 3 : ℝ) by norm_num]
        using hvol
    have hlocal := middle_localDensity_product_le_exp hQ a ha
      (fun i => (d i).val) hdpos
    have hweights : (∏ i, partWeight (d i)) *
        (3 : ℝ) ^ (∑ i : Fin 3, (d i).val.primeFactors.card) =
        ∏ i, weightedPartWeight (d i) := by
      simp only [weightedPartWeight, partWeight, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      ring
    have hprod_nonneg : 0 ≤ ∏ q ∈ Q,
        localDensityFactor q (fun i => (d i).val) a :=
      Finset.prod_nonneg (fun q _ => localDensityFactor_nonneg q _ a)
    have hweight_nonneg : 0 ≤ ∏ i, partWeight (d i) :=
      Finset.prod_nonneg (fun i _ => by
        unfold partWeight
        exact Real.rpow_nonneg (by positivity) _)
    rw [mul_div_assoc, localCount_div_cube_eq_localDensity_product_div hQ]
    calc
      fixedPartVolume (fun i => (d i).val) *
          ((∏ q ∈ Q, localDensityFactor q (fun i => (d i).val) a) /
            (goodModulus Q : ℝ))
          ≤ (∏ i, partWeight (d i)) *
              ((∏ q ∈ Q, localDensityFactor q (fun i => (d i).val) a) /
                (goodModulus Q : ℝ)) := by
            gcongr
      _ ≤ (∏ i, partWeight (d i)) *
            ((Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / q) *
              (3 : ℝ) ^ (∑ i : Fin 3, (d i).val.primeFactors.card)) /
              (goodModulus Q : ℝ)) := by
          gcongr
      _ = _ := by rw [← hweights]; ring
  calc
    (∑ d ∈ partTriples E \ partTriples D,
      fixedPartVolume (fun i => (d i).val) *
        (@localCount (fun i => (d i).val) (goodModulus Q) a
          ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 3)
        ≤ ∑ d ∈ partTriples E \ partTriples D,
            (∏ i, weightedPartWeight (d i)) *
              Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / q) /
              (goodModulus Q : ℝ) := Finset.sum_le_sum hterm
    _ = Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / q) *
          (∑ d ∈ partTriples E \ partTriples D,
            ∏ i, weightedPartWeight (d i)) /
            (goodModulus Q : ℝ) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      ring
    _ ≤ Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / q) *
          (3 * totalWeightedPartWeight ^ 2 * weightedPartTail D) /
            (goodModulus Q : ℝ) := by
      gcongr
      exact weightedMiddle_le_total_tail D E hDE

/-- The finite sieve and three sufficiently small contributions imply a
sparse progression of three-positive-summand values. -/
theorem sparseThreeSumProgression_of_sieveEstimates
    (h : HasSieveEstimates) : HasSparseThreeSumProgression := by
  obtain ⟨M, a, D, E, hM, ha, hDE, hcore, hmiddle, htail⟩ := h
  refine ⟨M, a, hM, ha, ?_⟩
  filter_upwards [hcore, hmiddle, htail] with N hc hm ht
  let c := ∑ d ∈ partTriples D,
    fixedPartCount (fun i => (d i).val) M a N
  let m := ∑ d ∈ partTriples E \ partTriples D,
    fixedPartCount (fun i => (d i).val) M a N
  let t := sieveTailCount E M a N
  have hcount : threeProgressionCount M a N ≤ c + m + t :=
    threeProgressionCount_le_sieve D E hDE M a N
  have hscaled := Nat.mul_le_mul_left (8 * M) hcount
  have hsum : 8 * M * (c + m + t) ≤ N := by
    have hc' : 4 * (8 * M * c) ≤ N := by
      calc
        4 * (8 * M * c) = 32 * M * c := by ring
        _ ≤ N := hc
    have hm' : 4 * (8 * M * m) ≤ N := by
      calc
        4 * (8 * M * m) = 32 * M * m := by ring
        _ ≤ N := hm
    have ht' : 4 * (8 * M * t) ≤ N := by
      calc
        4 * (8 * M * t) = 32 * M * t := by ring
        _ ≤ N := ht
    have hdist : 8 * M * (c + m + t) =
        8 * M * c + 8 * M * m + 8 * M * t := by ring
    rw [hdist]
    omega
  exact hscaled.trans hsum

theorem sieveEstimates : HasSieveEstimates := by
  classical
  let W := totalPartWeight
  let H := totalWeightedPartWeight
  obtain ⟨T, hT, hdecay⟩ :=
    exists_decay_threshold (W ^ 3) (1 / 64 : ℝ) (by norm_num)
  let A : ℝ := Real.exp (8 * (T + 1)) * (3 * H ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨D, hD⟩ :=
    exists_parts_with_scaled_weighted_tail A (1 / 64 : ℝ) hA (by norm_num)
  obtain ⟨Q, hQ, hsumLower, hsumUpper⟩ :=
    finite_goodPrime_batch (partValues D) (partValues_pos D) T hT
  obtain ⟨a, haM, ha⟩ := exists_good_noncube_progression hQ
  let M := goodModulus Q
  have hM : 0 < M := goodModulus_pos hQ
  letI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨E, hDE, htailSmall⟩ :=
    exists_larger_parts_for_sieve_estimate D M
  let S : ℝ := ∑ q ∈ Q, (1 : ℝ) / q
  have hexpCore : Real.exp (-2 * S) ≤ Real.exp (-2 * T) :=
    Real.exp_le_exp.mpr (by dsimp [S] at *; linarith)
  have hexpMiddle : Real.exp (8 * S) ≤ Real.exp (8 * (T + 1)) :=
    Real.exp_le_exp.mpr (by dsimp [S] at *; linarith)
  have hWD0 : 0 ≤ ∑ d ∈ D, partWeight d :=
    Finset.sum_nonneg (fun d _ => by unfold partWeight; positivity)
  have hWD : (∑ d ∈ D, partWeight d) ≤ W := finitePartWeight_le_total D
  have hWcube : (∑ d ∈ D, partWeight d) ^ 3 ≤ W ^ 3 :=
    pow_le_pow_left₀ hWD0 hWD 3
  have hcoreNumerator : Real.exp (-2 * S) *
      (∑ d ∈ D, partWeight d) ^ 3 < (1 / 32 : ℝ) := by
    calc
      Real.exp (-2 * S) * (∑ d ∈ D, partWeight d) ^ 3
          ≤ Real.exp (-2 * T) * W ^ 3 := by
            exact mul_le_mul hexpCore hWcube (pow_nonneg hWD0 3)
              (Real.exp_pos _).le
      _ = W ^ 3 * Real.exp (-(2 * T)) := by ring
      _ < 1 / 64 := hdecay
      _ < 1 / 32 := by norm_num
  have htail0 : 0 ≤ weightedPartTail D := weightedPartTail_nonneg D
  have hmiddleNumerator : Real.exp (8 * S) *
      (3 * H ^ 2 * weightedPartTail D) < (1 / 32 : ℝ) := by
    calc
      Real.exp (8 * S) * (3 * H ^ 2 * weightedPartTail D)
          ≤ Real.exp (8 * (T + 1)) *
              (3 * H ^ 2 * weightedPartTail D) :=
            mul_le_mul_of_nonneg_right hexpMiddle (by positivity)
      _ = A * weightedPartTail D := by dsimp [A]; ring
      _ < 1 / 64 := hD
      _ < 1 / 32 := by norm_num
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hdivEq (x : ℝ) : x / (M : ℝ) < 1 / (32 * (M : ℝ)) ↔
      x < (1 / 32 : ℝ) := by
    constructor <;> intro h
    · have hh := (div_lt_div_iff₀ hMreal (by positivity :
          (0 : ℝ) < 32 * (M : ℝ))).mp h
      nlinarith [ne_of_gt hMreal]
    · have hh := div_lt_div_of_pos_right h hMreal
      convert hh using 1 <;> ring
  let core : ℕ → ℕ := fun N => ∑ d ∈ partTriples D,
    fixedPartCount (fun i => (d i).val) M a N
  let middle : ℕ → ℕ := fun N => ∑ d ∈ partTriples E \ partTriples D,
    fixedPartCount (fun i => (d i).val) M a N
  have hcoreLimit := finite_fixedPartCount_asymptotic (partTriples D) M a
  have hmiddleLimit := finite_fixedPartCount_asymptotic
    (partTriples E \ partTriples D) M a
  have hcoreSmall :
      (∑ d ∈ partTriples D,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 3) <
        1 / (32 * (M : ℝ)) := by
    apply lt_of_le_of_lt (core_fixedPart_limit_le D Q hQ a ha)
    exact (hdivEq _).2 hcoreNumerator
  have hmiddleSmall :
      (∑ d ∈ partTriples E \ partTriples D,
        fixedPartVolume (fun i => (d i).val) *
          (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 3) <
        1 / (32 * (M : ℝ)) := by
    apply lt_of_le_of_lt (middle_fixedPart_limit_le D E hDE Q hQ a ha)
    exact (hdivEq _).2 hmiddleNumerator
  have hcoreEvent : ∀ᶠ N in Filter.atTop, 32 * M * core N ≤ N :=
    eventually_scaled_count_le_of_limit core M hM _ hcoreLimit hcoreSmall
  have hmiddleEvent : ∀ᶠ N in Filter.atTop, 32 * M * middle N ≤ N :=
    eventually_scaled_count_le_of_limit middle M hM _ hmiddleLimit hmiddleSmall
  have htailEvent : ∀ᶠ N in Filter.atTop,
      32 * M * sieveTailCount E M a N ≤ N :=
    Filter.Eventually.of_forall (fun N =>
      sieveTailCount_scaled_le E M a htailSmall.le N)
  exact ⟨M, a, D, E, hM, haM, hDE, hcoreEvent, hmiddleEvent, htailEvent⟩

theorem sparseThreeSumProgression : HasSparseThreeSumProgression :=
  sparseThreeSumProgression_of_sieveEstimates sieveEstimates

/- The positive one- and two-summand count is sublinear by `Parts`; the
additional zero value is harmless. -/
theorem atMostTwoCount_sublinear : SublinearCount atMostTwoCount := by
  intro C hC
  have hsmall := oneTwoSumsBelow_eventually_small (2 * C) (by omega)
  have hlarge : ∀ᶠ N in Filter.atTop, 2 * C ≤ N :=
    Filter.eventually_ge_atTop (2 * C)
  filter_upwards [hsmall, hlarge] with N hsmallN hlargeN
  have hcount := atMostTwoCount_le_one_add_oneTwoSumsBelow N
  have hscaled := Nat.mul_le_mul_left (2 * C) hcount
  simp only [mul_add, mul_one] at hscaled
  have hdouble : (2 * C) * atMostTwoCount N =
      2 * (C * atMostTwoCount N) := by ring
  rw [hdouble] at hscaled
  omega

/-- The paper's positive lower-density conclusion for the complement at r = 3. -/
theorem positiveLowerDensityComplement_three :
    HasPositiveLowerDensityComplementFor 3 := by
  obtain ⟨M, a, hM, ha, hthree⟩ := sparseThreeSumProgression
  exact positiveLowerDensity_of_progression_estimate hM ha hthree
    atMostTwoCount_sublinear

/-- The E940 r = 3 coinfinitude claim. -/
theorem coinfiniteFor_three : CoinfiniteFor 3 :=
  coinfiniteFor_of_positiveLowerDensity positiveLowerDensityComplement_three

end Erdos940
