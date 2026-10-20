import Erdos940.Quartic.JacobiTraceBridge

/-!
# Eleven constituents of the split-prime quartic trace

The 21 exponent vectors in the quartic Gauss trace consist of one quadratic
term, three complementary pairs, six mixed pairs, and one CM pair. This file
first records the finite regrouping independently of character theory.
-/

namespace Erdos940.Quartic

open scoped BigOperators
open NumberField

private def pairSlots : Fin 3 → Fin 4
  | 0 => 1
  | 1 => 2
  | _ => 3

private def mixedSlots : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | _ => (2, 3)

/-- The three representatives of complementary-pair exponent patterns. -/
def quarticPairRepresentative (k : Fin 3) : Fin 4 → Fin 4 :=
  fun i => if i = 0 ∨ i = pairSlots k then 1 else 3

/-- The six representatives of mixed exponent patterns. -/
def quarticMixedRepresentative (k : Fin 6) : Fin 4 → Fin 4 :=
  fun i => if i = (mixedSlots k).1 then 1
    else if i = (mixedSlots k).2 then 3 else 2

/-- Involution exchanging the two quartic orientations. -/
def quarticConjugateExponent (j : Fin 4 → Fin 4) : Fin 4 → Fin 4 :=
  fun i => if j i = 1 then 3 else if j i = 3 then 1 else j i

/-- Each of the eleven buckets of the 21-term trace. -/
def quarticElevenBucket : Fin 11 → Finset (Fin 4 → Fin 4)
  | 0 => {fun _ => 2}
  | 1 => {quarticPairRepresentative 0, quarticConjugateExponent (quarticPairRepresentative 0)}
  | 2 => {quarticPairRepresentative 1, quarticConjugateExponent (quarticPairRepresentative 1)}
  | 3 => {quarticPairRepresentative 2, quarticConjugateExponent (quarticPairRepresentative 2)}
  | 4 => {quarticMixedRepresentative 0, quarticConjugateExponent (quarticMixedRepresentative 0)}
  | 5 => {quarticMixedRepresentative 1, quarticConjugateExponent (quarticMixedRepresentative 1)}
  | 6 => {quarticMixedRepresentative 2, quarticConjugateExponent (quarticMixedRepresentative 2)}
  | 7 => {quarticMixedRepresentative 3, quarticConjugateExponent (quarticMixedRepresentative 3)}
  | 8 => {quarticMixedRepresentative 4, quarticConjugateExponent (quarticMixedRepresentative 4)}
  | 9 => {quarticMixedRepresentative 5, quarticConjugateExponent (quarticMixedRepresentative 5)}
  | _ => {fun _ => 1, fun _ => 3}

theorem quarticElevenBucket_partition :
    (Finset.univ.biUnion quarticElevenBucket) = quarticExponents := by
  decide

theorem quarticElevenBucket_pairwise_disjoint :
    ((Finset.univ : Finset (Fin 11)) : Set (Fin 11)).PairwiseDisjoint
      quarticElevenBucket := by
  intro i _ j _ hij
  change Disjoint (quarticElevenBucket i) (quarticElevenBucket j)
  fin_cases i <;> fin_cases j <;>
    (first | contradiction | decide)

/-- A finite, coefficient-independent 21-to-11 sum identity. -/
theorem quarticTrace_sum_eleven (f : (Fin 4 → Fin 4) → ℂ) :
    ∑ j ∈ quarticExponents, f j =
      ∑ k : Fin 11, ∑ j ∈ quarticElevenBucket k, f j := by
  rw [← quarticElevenBucket_partition]
  exact Finset.sum_biUnion quarticElevenBucket_pairwise_disjoint

/-- The eleven normalized Gauss constituents. -/
noncomputable def quarticElevenGaussConstituent
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (ψ : AddChar (ZMod q) ℂ) (a : Fin 4 → ZMod q) (k : Fin 11) : ℂ :=
  ∑ j ∈ quarticElevenBucket k, quarticGaussTerm q χ ψ a j

theorem quarticGaussTrace_eq_eleven
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (ψ : AddChar (ZMod q) ℂ) (a : Fin 4 → ZMod q) :
    ∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j =
      ∑ k : Fin 11, quarticElevenGaussConstituent q χ ψ a k := by
  exact quarticTrace_sum_eleven _

/-- The radicand attached to a complementary-pair exponent vector. -/
def quarticPairRadicand (q : ℕ) (a : Fin 4 → ZMod q)
    (j : Fin 4 → Fin 4) : ZMod q :=
  ∏ i : Fin 4, a i ^ (if j i = 1 then 3 else 1)

/-- The negative radicand attached to a mixed exponent vector. -/
def quarticMixedRadicand (q : ℕ) (a : Fin 4 → ZMod q)
    (j : Fin 4 → Fin 4) : ZMod q :=
  -(∏ i : Fin 4, a i ^ (if j i = 1 then 3 else if j i = 3 then 1 else 2))

private theorem pair_radicands_mul
    (q : ℕ) (a : Fin 4 → ZMod q) (k : Fin 3) :
    quarticPairRadicand q a (quarticPairRepresentative k) *
        quarticPairRadicand q a
          (quarticConjugateExponent (quarticPairRepresentative k)) =
      (∏ i : Fin 4, a i) ^ 4 := by
  fin_cases k <;>
    simp [quarticPairRadicand, quarticPairRepresentative,
      quarticConjugateExponent, pairSlots, Fin.prod_univ_succ] <;> ring

private theorem mixed_radicands_mul
    (q : ℕ) (a : Fin 4 → ZMod q) (k : Fin 6) :
    quarticMixedRadicand q a (quarticMixedRepresentative k) *
        quarticMixedRadicand q a
          (quarticConjugateExponent (quarticMixedRepresentative k)) =
      (∏ i : Fin 4, a i) ^ 4 := by
  fin_cases k <;>
    simp [quarticMixedRadicand, quarticMixedRepresentative,
      quarticConjugateExponent, mixedSlots, Fin.prod_univ_succ] <;> ring

theorem quarticGaussTerm_pair_radicand
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (j : Fin 4 → Fin 4)
    (h1 : exponentMultiplicity j 1 = 2)
    (h2 : exponentMultiplicity j 2 = 0)
    (h3 : exponentMultiplicity j 3 = 2) :
    quarticGaussTerm q χ ψ a j = χ (quarticPairRadicand q a j) := by
  obtain ⟨σ, rfl⟩ := pair_exponent_exists_permutation j h1 h2 h3
  rw [quarticGaussTerm_permutation,
    quarticGaussTerm_pair_canonical q χ hχ ψ hψ]
  congr 1
  unfold quarticPairRadicand
  conv_rhs =>
    rw [← Equiv.prod_comp σ.symm (fun i : Fin 4 =>
      a i ^ (if quarticPairExponent (σ i) = 1 then 3 else 1))]
  simp [quarticPairExponent, Fin.prod_univ_succ]
  ring

theorem quarticGaussTerm_mixed_radicand
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (j : Fin 4 → Fin 4)
    (h1 : exponentMultiplicity j 1 = 1)
    (h2 : exponentMultiplicity j 2 = 2)
    (h3 : exponentMultiplicity j 3 = 1) :
    quarticGaussTerm q χ ψ a j = χ (quarticMixedRadicand q a j) := by
  obtain ⟨σ, rfl⟩ := mixed_exponent_exists_permutation j h1 h2 h3
  rw [quarticGaussTerm_permutation,
    quarticGaussTerm_mixed_canonical q χ hχ ψ hψ]
  congr 1
  unfold quarticMixedRadicand
  conv_rhs =>
    rw [← Equiv.prod_comp σ.symm (fun i : Fin 4 =>
      a i ^ (if quarticMixedExponent (σ i) = 1 then 3
        else if quarticMixedExponent (σ i) = 3 then 1 else 2))]
  simp [quarticMixedExponent, Fin.prod_univ_succ]
  ring

private theorem pair_rep_pattern (k : Fin 3) :
    exponentMultiplicity (quarticPairRepresentative k) 1 = 2 ∧
    exponentMultiplicity (quarticPairRepresentative k) 2 = 0 ∧
    exponentMultiplicity (quarticPairRepresentative k) 3 = 2 := by
  fin_cases k <;> decide

private theorem pair_conj_pattern (k : Fin 3) :
    exponentMultiplicity
        (quarticConjugateExponent (quarticPairRepresentative k)) 1 = 2 ∧
    exponentMultiplicity
        (quarticConjugateExponent (quarticPairRepresentative k)) 2 = 0 ∧
    exponentMultiplicity
        (quarticConjugateExponent (quarticPairRepresentative k)) 3 = 2 := by
  fin_cases k <;> decide

private theorem mixed_rep_pattern (k : Fin 6) :
    exponentMultiplicity (quarticMixedRepresentative k) 1 = 1 ∧
    exponentMultiplicity (quarticMixedRepresentative k) 2 = 2 ∧
    exponentMultiplicity (quarticMixedRepresentative k) 3 = 1 := by
  fin_cases k <;> decide

private theorem mixed_conj_pattern (k : Fin 6) :
    exponentMultiplicity
        (quarticConjugateExponent (quarticMixedRepresentative k)) 1 = 1 ∧
    exponentMultiplicity
        (quarticConjugateExponent (quarticMixedRepresentative k)) 2 = 2 ∧
    exponentMultiplicity
        (quarticConjugateExponent (quarticMixedRepresentative k)) 3 = 1 := by
  fin_cases k <;> decide

private theorem pair_rep_ne_conj (k : Fin 3) :
    quarticPairRepresentative k ≠
      quarticConjugateExponent (quarticPairRepresentative k) := by
  fin_cases k <;> decide

private theorem mixed_rep_ne_conj (k : Fin 6) :
    quarticMixedRepresentative k ≠
      quarticConjugateExponent (quarticMixedRepresentative k) := by
  fin_cases k <;> decide

/-- A complementary-pair bucket is the sum of its two quartic-residue values. -/
theorem quarticEleven_pair_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) (k : Fin 3) :
    quarticGaussTerm q χ ψ a (quarticPairRepresentative k) +
        quarticGaussTerm q χ ψ a
          (quarticConjugateExponent (quarticPairRepresentative k)) =
      χ (quarticPairRadicand q a (quarticPairRepresentative k)) +
        χ (quarticPairRadicand q a
          (quarticConjugateExponent (quarticPairRepresentative k))) := by
  rw [quarticGaussTerm_pair_radicand q χ hχ ψ hψ a _
    (pair_rep_pattern k).1 (pair_rep_pattern k).2.1 (pair_rep_pattern k).2.2,
    quarticGaussTerm_pair_radicand q χ hχ ψ hψ a _
      (pair_conj_pattern k).1 (pair_conj_pattern k).2.1 (pair_conj_pattern k).2.2]

/-- A mixed bucket is the sum of its two negative quartic-residue values. -/
theorem quarticEleven_mixed_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) (k : Fin 6) :
    quarticGaussTerm q χ ψ a (quarticMixedRepresentative k) +
        quarticGaussTerm q χ ψ a
          (quarticConjugateExponent (quarticMixedRepresentative k)) =
      χ (quarticMixedRadicand q a (quarticMixedRepresentative k)) +
        χ (quarticMixedRadicand q a
          (quarticConjugateExponent (quarticMixedRepresentative k))) := by
  rw [quarticGaussTerm_mixed_radicand q χ hχ ψ hψ a _
    (mixed_rep_pattern k).1 (mixed_rep_pattern k).2.1 (mixed_rep_pattern k).2.2,
    quarticGaussTerm_mixed_radicand q χ hχ ψ hψ a _
      (mixed_conj_pattern k).1 (mixed_conj_pattern k).2.1
      (mixed_conj_pattern k).2.2]

private theorem quarticCharacterValue_norm_one
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ4 : χ ^ 4 = 1) (x : ZMod q) (hx : x ≠ 0) :
    ‖χ x‖ = 1 := by
  let u : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
  have hu : (u : ZMod q) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
  have hpow : χ x ^ 4 = 1 := by
    have h := congrArg (fun θ : MulChar (ZMod q) ℂ => θ (u : ZMod q)) hχ4
    rw [MulChar.pow_apply_coe] at h
    simpa [hu, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)] using h
  exact Complex.norm_eq_one_of_pow_eq_one hpow (by decide)

private theorem quarticGauss_norm_sqrt
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : χ ≠ 1) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt q := by
  have hmul := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq χ ψ] at hmul
  have hnorm := congrArg norm hmul
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (q : ℝ) := by
    simpa only [norm_mul, norm_star, Complex.norm_natCast, pow_two, ZMod.card] using hnorm
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q), Real.sqrt_nonneg (q : ℝ),
    norm_nonneg (gaussSum χ ψ)]

private theorem quarticCharPower_ne_one
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (k : Fin 4) (hk : k ≠ 0) :
    χ ^ (k : ℕ) ≠ 1 := by
  intro he
  have hd := orderOf_dvd_of_pow_eq_one he
  fin_cases k <;> norm_num [hχ] at *

/-- Every normalized term in the 21-term quartic trace has modulus one. -/
theorem quarticGaussTerm_norm_one
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) (j : Fin 4 → Fin 4)
    (hj : j ∈ quarticExponents) :
    ‖quarticGaussTerm q χ ψ a j‖ = 1 := by
  have hjnz : ∀ i, j i ≠ 0 := (Finset.mem_filter.mp hj).2.1
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hterm (i : Fin 4) :
      ‖(χ ^ (j i : ℕ))⁻¹ (a i) * gaussSum (χ ^ (j i : ℕ)) ψ‖ =
        Real.sqrt q := by
    have hpow4 : (χ ^ (j i : ℕ)) ^ 4 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hχ4, one_pow]
    have hchar : ‖(χ ^ (j i : ℕ))⁻¹ (a i)‖ = 1 := by
      rw [MulChar.inv_apply_eq_inv', norm_inv]
      rw [quarticCharacterValue_norm_one q (χ ^ (j i : ℕ)) hpow4 (a i) (ha i)]
      simp
    rw [norm_mul, hchar, one_mul]
    exact quarticGauss_norm_sqrt q (χ ^ (j i : ℕ))
      (quarticCharPower_ne_one q χ hχ (j i) (hjnz i)) ψ hψ
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  unfold quarticGaussTerm
  rw [norm_div, norm_prod]
  simp_rw [hterm]
  simp only [Finset.prod_const, Finset.card_fin, Complex.norm_pow, Complex.norm_natCast]
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 4 = (q : ℝ) ^ 2 := by
    calc
      _ = ((Real.sqrt (q : ℝ)) ^ 2) ^ 2 := by ring
      _ = (q : ℝ) ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [hsqrt]
  field_simp

theorem quarticGaussTrace_norm_le_21
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    ‖∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j‖ ≤ 21 := by
  exact quarticTrace_norm_le_21 _ (fun j hj =>
    le_of_eq (quarticGaussTerm_norm_one q χ hχ ψ hψ a ha j hj))

private theorem quarticCharacter_inverse_of_radicands
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) (r s : ZMod q)
    (hrs : r * s = (∏ i : Fin 4, a i) ^ 4) :
    χ s = (χ r)⁻¹ := by
  have hDnz : (∏ i : Fin 4, a i) ≠ 0 := by
    simp [Finset.prod_ne_zero_iff, ha]
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hD4 : χ (∏ i : Fin 4, a i) ^ 4 = 1 := by
    rw [← χ.pow_apply' (by decide : 4 ≠ 0), hχ4,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hDnz)]
  have hmul : χ r * χ s = 1 := by
    rw [← map_mul, hrs, map_pow, hD4]
  exact (inv_eq_of_mul_eq_one_right hmul).symm

/-- The two rational radicands in one complementary-pair bucket. -/
noncomputable def quarticPairCharacterTrace
    (q : ℕ) (χ : MulChar (ZMod q) ℂ) (a : Fin 4 → ZMod q)
    (k : Fin 3) : ℂ :=
  χ (quarticPairRadicand q a (quarticPairRepresentative k)) +
    χ (quarticPairRadicand q a
      (quarticConjugateExponent (quarticPairRepresentative k)))

/-- The two negative rational radicands in one mixed bucket. -/
noncomputable def quarticMixedCharacterTrace
    (q : ℕ) (χ : MulChar (ZMod q) ℂ) (a : Fin 4 → ZMod q)
    (k : Fin 6) : ℂ :=
  χ (quarticMixedRadicand q a (quarticMixedRepresentative k)) +
    χ (quarticMixedRadicand q a
      (quarticConjugateExponent (quarticMixedRepresentative k)))

theorem quarticPairCharacterTrace_eq_inverse
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) (k : Fin 3) :
    quarticPairCharacterTrace q χ a k =
      χ (quarticPairRadicand q a (quarticPairRepresentative k)) +
        (χ (quarticPairRadicand q a (quarticPairRepresentative k)))⁻¹ := by
  unfold quarticPairCharacterTrace
  rw [quarticCharacter_inverse_of_radicands q χ hχ a ha _ _
    (pair_radicands_mul q a k)]

theorem quarticMixedCharacterTrace_eq_inverse
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) (k : Fin 6) :
    quarticMixedCharacterTrace q χ a k =
      χ (quarticMixedRadicand q a (quarticMixedRepresentative k)) +
        (χ (quarticMixedRadicand q a (quarticMixedRepresentative k)))⁻¹ := by
  unfold quarticMixedCharacterTrace
  rw [quarticCharacter_inverse_of_radicands q χ hχ a ha _ _
    (mixed_radicands_mul q a k)]

/-- A rational residue, lifted through its natural representative, has the
same quartic symbol at the selected Gaussian prime as its quartic character. -/
noncomputable def quarticRationalPrimeSymbolValue
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (r : ZMod q) (hr : r ≠ 0) : ℂ := by
  let z : GaussianInt := (r.val : ℕ)
  have hz : ρ z ≠ 0 := by simpa [z] using hr
  let P := gaussianPrimeIdealOfReduction q ρ π hπ0 hρπ
  let h2 := gaussianPrimeIdealOfReduction_coprime_four
    q hqmod ρ π hπ0 hρπ
  let hR := gaussianPrimeIdealOfReduction_not_mem
    q ρ π hπ0 hρπ z hz
  exact fourthIntegerRingToComplex
    (((gaussianQuarticPrimeSymbol (gaussianFourthIntegerRingEquiv z)
        P h2 hR : rootsOfUnity 4 (𝓞 GaussianField)) :
        (𝓞 GaussianField)ˣ) : 𝓞 GaussianField)

theorem quarticRationalPrimeSymbolValue_eq_character
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (r : ZMod q) (hr : r ≠ 0) :
    quarticRationalPrimeSymbolValue q hqmod ρ π hπ0 hρπ r hr = χ r := by
  let z : GaussianInt := (r.val : ℕ)
  have hz : ρ z = r := by simp [z]
  have hzr : ρ z ≠ 0 := hz ▸ hr
  have h2 := gaussianPrimeIdealOfReduction_coprime_four
    q hqmod ρ π hπ0 hρπ
  have hR := gaussianPrimeIdealOfReduction_not_mem
    q ρ π hπ0 hρπ z hzr
  unfold quarticRationalPrimeSymbolValue
  simpa only [hz] using
    (gaussianQuarticPrimeSymbol_complex_eq_character
      q hqmod ρ π hπ0 hρπ χ hχ hρchar z hzr h2 hR)

/-- The two orientations as a symbol and its inverse at the chosen prime. -/
noncomputable def quarticRationalPrimeSymbolTrace
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (r : ZMod q) (hr : r ≠ 0) : ℂ :=
  quarticRationalPrimeSymbolValue q hqmod ρ π hπ0 hρπ r hr +
    (quarticRationalPrimeSymbolValue q hqmod ρ π hπ0 hρπ r hr)⁻¹

theorem quarticPairRadicand_ne_zero
    (q : ℕ) [Fact q.Prime] (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (k : Fin 3) :
    quarticPairRadicand q a (quarticPairRepresentative k) ≠ 0 := by
  unfold quarticPairRadicand
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs <;> simp [ha i]

theorem quarticMixedRadicand_ne_zero
    (q : ℕ) [Fact q.Prime] (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (k : Fin 6) :
    quarticMixedRadicand q a (quarticMixedRepresentative k) ≠ 0 := by
  unfold quarticMixedRadicand
  simp only [neg_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs <;> simp [ha i]

theorem quarticPairCharacterTrace_eq_prime_symbol_trace
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) (k : Fin 3) :
    quarticPairCharacterTrace q χ a k =
      quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
        (quarticPairRadicand q a (quarticPairRepresentative k))
        (quarticPairRadicand_ne_zero q a ha k) := by
  rw [quarticPairCharacterTrace_eq_inverse q χ hχ a ha k]
  unfold quarticRationalPrimeSymbolTrace
  rw [quarticRationalPrimeSymbolValue_eq_character
    q hqmod ρ π hπ0 hρπ χ hχ hρchar]

theorem quarticMixedCharacterTrace_eq_prime_symbol_trace
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) (k : Fin 6) :
    quarticMixedCharacterTrace q χ a k =
      quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
        (quarticMixedRadicand q a (quarticMixedRepresentative k))
        (quarticMixedRadicand_ne_zero q a ha k) := by
  rw [quarticMixedCharacterTrace_eq_inverse q χ hχ a ha k]
  unfold quarticRationalPrimeSymbolTrace
  rw [quarticRationalPrimeSymbolValue_eq_character
    q hqmod ρ π hπ0 hρπ χ hχ hρchar]

/-- The CM angular trace attached to a Gaussian prime above `q`. -/
noncomputable def quarticCMCharacterTrace
    (q : ℕ) (χ : MulChar (ZMod q) ℂ) (a : Fin 4 → ZMod q)
    (π : GaussianInt) : ℂ :=
  χ⁻¹ (∏ i, a i) * ((π : ℂ) ^ 2 / (q : ℂ)) +
    χ (∏ i, a i) * (star (π : ℂ) ^ 2 / (q : ℂ))

/-- The explicit eleven terms of the split-prime expansion (Eq. 5). -/
noncomputable def quarticElevenCharacterConstituent
    (q : ℕ) (χ : MulChar (ZMod q) ℂ) (a : Fin 4 → ZMod q)
    (π : GaussianInt) : Fin 11 → ℂ
  | 0 => (χ ^ 2) (∏ i, a i)
  | 1 => quarticPairCharacterTrace q χ a 0
  | 2 => quarticPairCharacterTrace q χ a 1
  | 3 => quarticPairCharacterTrace q χ a 2
  | 4 => quarticMixedCharacterTrace q χ a 0
  | 5 => quarticMixedCharacterTrace q χ a 1
  | 6 => quarticMixedCharacterTrace q χ a 2
  | 7 => quarticMixedCharacterTrace q χ a 3
  | 8 => quarticMixedCharacterTrace q χ a 4
  | 9 => quarticMixedCharacterTrace q χ a 5
  | _ => quarticCMCharacterTrace q χ a π

/-- The same eleven terms, with each finite-order constituent written as a
Gaussian prime-ideal symbol and its inverse. -/
noncomputable def quarticElevenPrimeSymbolConstituent
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) : Fin 11 → ℂ
  | 0 => (χ ^ 2) (∏ i, a i)
  | 1 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticPairRadicand q a (quarticPairRepresentative 0))
      (quarticPairRadicand_ne_zero q a ha 0)
  | 2 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticPairRadicand q a (quarticPairRepresentative 1))
      (quarticPairRadicand_ne_zero q a ha 1)
  | 3 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticPairRadicand q a (quarticPairRepresentative 2))
      (quarticPairRadicand_ne_zero q a ha 2)
  | 4 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticMixedRadicand q a (quarticMixedRepresentative 0))
      (quarticMixedRadicand_ne_zero q a ha 0)
  | 5 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticMixedRadicand q a (quarticMixedRepresentative 1))
      (quarticMixedRadicand_ne_zero q a ha 1)
  | 6 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticMixedRadicand q a (quarticMixedRepresentative 2))
      (quarticMixedRadicand_ne_zero q a ha 2)
  | 7 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticMixedRadicand q a (quarticMixedRepresentative 3))
      (quarticMixedRadicand_ne_zero q a ha 3)
  | 8 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticMixedRadicand q a (quarticMixedRepresentative 4))
      (quarticMixedRadicand_ne_zero q a ha 4)
  | 9 => quarticRationalPrimeSymbolTrace q hqmod ρ π hπ0 hρπ
      (quarticMixedRadicand q a (quarticMixedRepresentative 5))
      (quarticMixedRadicand_ne_zero q a ha 5)
  | _ => quarticCMCharacterTrace q χ a π

theorem quarticElevenCharacterConstituent_eq_prime_symbol
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) (k : Fin 11) :
    quarticElevenCharacterConstituent q χ a π k =
      quarticElevenPrimeSymbolConstituent q hqmod ρ π hπ0 hρπ χ a ha k := by
  fin_cases k
  case «0» => rfl
  case «1» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticPairCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 0
  case «2» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticPairCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 1
  case «3» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticPairCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 2
  case «4» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticMixedCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 0
  case «5» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticMixedCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 1
  case «6» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticMixedCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 2
  case «7» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticMixedCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 3
  case «8» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticMixedCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 4
  case «9» =>
    simpa [quarticElevenCharacterConstituent,
      quarticElevenPrimeSymbolConstituent] using
      quarticMixedCharacterTrace_eq_prime_symbol_trace
        q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha 5
  case «10» => rfl

private theorem pairBucket_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) (k : Fin 3) :
    ∑ j ∈ {quarticPairRepresentative k,
        quarticConjugateExponent (quarticPairRepresentative k)},
      quarticGaussTerm q χ ψ a j = quarticPairCharacterTrace q χ a k := by
  rw [Finset.sum_pair (pair_rep_ne_conj k)]
  exact quarticEleven_pair_character q χ hχ ψ hψ a k

private theorem mixedBucket_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q) (k : Fin 6) :
    ∑ j ∈ {quarticMixedRepresentative k,
        quarticConjugateExponent (quarticMixedRepresentative k)},
      quarticGaussTerm q χ ψ a j = quarticMixedCharacterTrace q χ a k := by
  rw [Finset.sum_pair (mixed_rep_ne_conj k)]
  exact quarticEleven_mixed_character q χ hχ ψ hψ a k

private theorem cmBucket_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (π : GaussianInt) (hJ : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2) :
    ∑ j ∈ {(fun _ : Fin 4 => (1 : Fin 4)), (fun _ => 3)},
      quarticGaussTerm q χ ψ a j = quarticCMCharacterTrace q χ a π := by
  rw [Finset.sum_pair (by decide : (fun _ : Fin 4 => (1 : Fin 4)) ≠ fun _ => 3)]
  rw [quarticGaussTerm_all_one q χ hχ ψ hψ a, hJ,
    quartic_all_three_trace_of_jacobi_square q χ hχ π hJ ψ hψ a]
  rfl

theorem quarticElevenGaussConstituent_eq_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (π : GaussianInt) (hJ : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2)
    (k : Fin 11) :
    quarticElevenGaussConstituent q χ ψ a k =
      quarticElevenCharacterConstituent q χ a π k := by
  fin_cases k
  case «0» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent, Finset.sum_singleton] using
      quarticGaussTerm_all_two q χ hχ ψ hψ a
  case «1» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      pairBucket_character q χ hχ ψ hψ a 0
  case «2» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      pairBucket_character q χ hχ ψ hψ a 1
  case «3» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      pairBucket_character q χ hχ ψ hψ a 2
  case «4» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      mixedBucket_character q χ hχ ψ hψ a 0
  case «5» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      mixedBucket_character q χ hχ ψ hψ a 1
  case «6» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      mixedBucket_character q χ hχ ψ hψ a 2
  case «7» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      mixedBucket_character q χ hχ ψ hψ a 3
  case «8» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      mixedBucket_character q χ hχ ψ hψ a 4
  case «9» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      mixedBucket_character q χ hχ ψ hψ a 5
  case «10» =>
    simpa [quarticElevenGaussConstituent, quarticElevenBucket,
      quarticElevenCharacterConstituent] using
      cmBucket_character q χ hχ ψ hψ a π hJ

/-- Exact 21-to-11 character regrouping of the normalized quartic trace. -/
theorem quarticGaussTrace_eq_eleven_characters
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (π : GaussianInt) (hJ : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2) :
    ∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j =
      ∑ k : Fin 11, quarticElevenCharacterConstituent q χ a π k := by
  rw [quarticGaussTrace_eq_eleven]
  congr 1
  funext k
  exact quarticElevenGaussConstituent_eq_character q χ hχ ψ hψ a π hJ k

/-- Eq. (5) at a selected split Gaussian prime, before replacing inverse
symbols by the symbols at its conjugate prime. -/
theorem quarticGaussTrace_eq_eleven_prime_symbols
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπ0 : π ≠ 0) (hρπ : ρ π = 0)
    (χ : MulChar (ZMod q) ℂ) (hχ : orderOf χ = 4)
    (hρchar : ∀ x : ZMod q,
      ρ (quarticGaussianLift q χ hχ x) = x ^ ((q - 1) / 4))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0)
    (hJ : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2) :
    ∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j =
      ∑ k : Fin 11,
        quarticElevenPrimeSymbolConstituent q hqmod ρ π hπ0 hρπ χ a ha k := by
  rw [quarticGaussTrace_eq_eleven_characters q χ hχ ψ hψ a π hJ]
  congr 1
  funext k
  exact quarticElevenCharacterConstituent_eq_prime_symbol
    q hqmod ρ π hπ0 hρπ χ hχ hρchar a ha k

end Erdos940.Quartic
