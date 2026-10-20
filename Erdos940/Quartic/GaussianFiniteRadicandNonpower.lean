import Erdos940.Quartic.GaussianFiniteCharacterNontrivial
import Erdos940.Quartic.GaussianFiniteConstituentTrace
import Erdos940.Quartic.SelectorIntegration

/-!
# Nonpower radicands of the nine finite quartic constituents

The complementary-pair constituents use the nonsquare product hypothesis;
the mixed constituents use the second regularity clause. All radicands here
are signed integers so the nontrivial Gaussian character theorem applies.
-/

open scoped NumberField Classical BigOperators

namespace Erdos940.Quartic

private theorem gaussianInteger_fourth_components (z : GaussianInt) :
    ((z ^ 4).re : ℚ) = gaussianFourthReal (z.re : ℚ) (z.im : ℚ) ∧
      ((z ^ 4).im : ℚ) = gaussianFourthImag (z.re : ℚ) (z.im : ℚ) := by
  constructor <;>
    simp [gaussianFourthReal, gaussianFourthImag, pow_succ,
      Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-- A fourth power in the Gaussian integer ring supplies the rational
Gaussian-coordinate witness used by the radicand obstruction lemmas. -/
theorem gaussianFourthCoordinateWitness_of_integer_fourth_power
    (R : ℤ) (h : ∃ v : 𝓞 GaussianField,
      v ^ 4 = (R : 𝓞 GaussianField)) :
    ∃ a b : ℚ,
      gaussianFourthReal a b = (R : ℚ) ∧ gaussianFourthImag a b = 0 := by
  obtain ⟨v, hv⟩ := h
  let z : GaussianInt := gaussianFourthIntegerRingEquiv.symm v
  have hz : z ^ 4 = (R : GaussianInt) := by
    apply gaussianFourthIntegerRingEquiv.injective
    simpa [z] using hv
  obtain ⟨hre, him⟩ := gaussianInteger_fourth_components z
  refine ⟨(z.re : ℚ), (z.im : ℚ), ?_, ?_⟩
  · rw [hz] at hre
    simpa using hre.symm
  · rw [hz] at him
    simpa using him.symm

/-- Integer numerator of a complementary-pair finite constituent. -/
def finitePairRadicand (d : Fin 4 → CanonicalParts)
    (j : Fin 4 → Fin 4) : ℤ :=
  ∏ i : Fin 4, ((d i).val : ℤ) ^ (if j i = 1 then 3 else 1)

/-- Integer numerator of a mixed finite constituent, including its sign. -/
def finiteMixedRadicand (d : Fin 4 → CanonicalParts)
    (j : Fin 4 → Fin 4) : ℤ :=
  -(∏ i : Fin 4, ((d i).val : ℤ) ^
      (if j i = 1 then 3 else if j i = 3 then 1 else 2))

/-- The signed rational-integer radicands of the nine finite-order
constituents. Indices zero and ten are unused defaults. -/
def finiteConstituentRadicand
    (d : Fin 4 → CanonicalParts) : Fin 11 → ℤ
  | 0 => 1
  | 1 => finitePairRadicand d (quarticPairRepresentative 0)
  | 2 => finitePairRadicand d (quarticPairRepresentative 1)
  | 3 => finitePairRadicand d (quarticPairRepresentative 2)
  | 4 => finiteMixedRadicand d (quarticMixedRepresentative 0)
  | 5 => finiteMixedRadicand d (quarticMixedRepresentative 1)
  | 6 => finiteMixedRadicand d (quarticMixedRepresentative 2)
  | 7 => finiteMixedRadicand d (quarticMixedRepresentative 3)
  | 8 => finiteMixedRadicand d (quarticMixedRepresentative 4)
  | 9 => finiteMixedRadicand d (quarticMixedRepresentative 5)
  | _ => 1

/-- Reduction of an integer constituent numerator is the exact radicand
in the finite-field trace decomposition. -/
theorem finiteConstituentRadicand_cast
    (d : Fin 4 → CanonicalParts) (p : ℕ) (j : Fin 11) :
    (finiteConstituentRadicand d j : ZMod p) =
      quarticFiniteBucketRadicand p
        (fun i => ((d i).val : ZMod p)) j := by
  fin_cases j <;>
    simp [finiteConstituentRadicand, quarticFiniteBucketRadicand,
      finitePairRadicand, finiteMixedRadicand,
      quarticPairRadicand, quarticMixedRadicand]

private theorem canonicalCoefficient_pos (d : Fin 4 → CanonicalParts) (i : Fin 4) :
    (0 : ℚ) < ((d i).val : ℚ) := by
  exact_mod_cast (d i).property.pos

private theorem regularProduct_nonsquare
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d) :
    ¬ IsSquare (∏ i : Fin 4, ((d i).val : ℚ)) := by
  rintro ⟨x, hx⟩
  apply hreg
  left
  exact ⟨x, by simpa [pow_two] using hx.symm⟩

private theorem finitePairRadicand_rational
    (d : Fin 4 → CanonicalParts) (j : Fin 4 → Fin 4) :
    (finitePairRadicand d j : ℚ) =
      complementaryRadicand (fun i => ((d i).val : ℚ))
        (Finset.univ.filter (fun i => j i = 1)) := by
  simp [finitePairRadicand, complementaryRadicand]

theorem finitePairRadicand_pos
    (d : Fin 4 → CanonicalParts) (j : Fin 4 → Fin 4) :
    0 < finitePairRadicand d j := by
  unfold finitePairRadicand
  apply Finset.prod_pos
  intro i _
  exact pow_pos (by exact_mod_cast (d i).property.pos) _

theorem finitePairRadicand_not_gaussian_fourth_power
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (j : Fin 4 → Fin 4) :
    ¬ ∃ v : 𝓞 GaussianField,
      v ^ 4 = (finitePairRadicand d j : 𝓞 GaussianField) := by
  intro hfourth
  obtain ⟨a, b, hre, him⟩ :=
    gaussianFourthCoordinateWitness_of_integer_fourth_power
      (finitePairRadicand d j) hfourth
  have hpos : 0 < complementaryRadicand
      (fun i => ((d i).val : ℚ))
      (Finset.univ.filter (fun i => j i = 1)) := by
    rw [← finitePairRadicand_rational]
    exact_mod_cast finitePairRadicand_pos d j
  have hd : ∀ i, ((d i).val : ℚ) ≠ 0 := by
    intro i
    exact (canonicalCoefficient_pos d i).ne'
  exact complementaryRadicand_not_gaussian_fourth_power
    (fun i => ((d i).val : ℚ))
    (Finset.univ.filter (fun i => j i = 1)) hpos
    (regularProduct_nonsquare d hreg) hd
    ⟨a, b, by simpa only [← finitePairRadicand_rational] using hre, him⟩

private theorem mixedRepresentative_exists_permutation (k : Fin 6) :
    ∃ σ : Equiv.Perm (Fin 4),
      quarticMixedRepresentative k =
        fun i => quarticMixedExponent (σ i) := by
  apply mixed_exponent_exists_permutation
  all_goals fin_cases k <;> decide

private theorem finiteMixedRadicand_rational_permutation
    (d : Fin 4 → CanonicalParts) (σ : Equiv.Perm (Fin 4)) :
    (finiteMixedRadicand d (fun i => quarticMixedExponent (σ i)) : ℚ) =
      -mixedRadicand (fun i => ((d i).val : ℚ))
        (σ.symm 0) (σ.symm 1) (σ.symm 2) (σ.symm 3) := by
  unfold finiteMixedRadicand mixedRadicand
  push_cast
  conv_lhs =>
    rw [← Equiv.prod_comp σ.symm (fun i : Fin 4 =>
      ((d i).val : ℚ) ^
        (if quarticMixedExponent (σ i) = 1 then 3
         else if quarticMixedExponent (σ i) = 3 then 1 else 2))]
  simp [quarticMixedExponent, Fin.prod_univ_succ]
  ring

private theorem mixedRadicand_regular_of_permutation
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (σ : Equiv.Perm (Fin 4)) :
    ¬ ∃ t : ℚ,
      mixedRadicand (fun i => ((d i).val : ℚ))
        (σ.symm 0) (σ.symm 1) (σ.symm 2) (σ.symm 3) = 4 * t ^ 4 := by
  rintro ⟨t, ht⟩
  apply hreg
  right
  let τ : Equiv.Perm (Fin 4) := (Equiv.swap 0 1).trans σ.symm
  refine ⟨τ, ⟨t, ?_⟩⟩
  have hswap2 : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := by decide
  have hswap3 : (Equiv.swap (0 : Fin 4) 1) 3 = 3 := by decide
  simpa [τ, hswap2, hswap3, MixedExceptional, mixedRadicand,
    mul_comm, mul_left_comm, mul_assoc]
    using ht

theorem finiteMixedRadicand_not_gaussian_fourth_power
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (k : Fin 6) :
    ¬ ∃ v : 𝓞 GaussianField,
      v ^ 4 = (finiteMixedRadicand d (quarticMixedRepresentative k) :
        𝓞 GaussianField) := by
  obtain ⟨σ, hσ⟩ := mixedRepresentative_exists_permutation k
  let M := mixedRadicand (fun i => ((d i).val : ℚ))
    (σ.symm 0) (σ.symm 1) (σ.symm 2) (σ.symm 3)
  have hpos : 0 < M := by
    have h0 := canonicalCoefficient_pos d (σ.symm 0)
    have h1 := canonicalCoefficient_pos d (σ.symm 1)
    have h2 := canonicalCoefficient_pos d (σ.symm 2)
    have h3 := canonicalCoefficient_pos d (σ.symm 3)
    dsimp [M, mixedRadicand]
    positivity
  have hregular : ¬ ∃ t : ℚ, M = 4 * t ^ 4 :=
    mixedRadicand_regular_of_permutation d hreg σ
  have hR : (finiteMixedRadicand d (quarticMixedRepresentative k) : ℚ) =
      -M := by
    rw [hσ]
    exact finiteMixedRadicand_rational_permutation d σ
  intro hfourth
  obtain ⟨a, b, hre, him⟩ :=
    gaussianFourthCoordinateWitness_of_integer_fourth_power
      (finiteMixedRadicand d (quarticMixedRepresentative k)) hfourth
  exact mixedRadicand_not_negative_gaussian_fourth_power
    (fun i => ((d i).val : ℚ))
    (σ.symm 0) (σ.symm 1) (σ.symm 2) (σ.symm 3)
    hpos hregular
    ⟨a, b, by simpa only [hR] using hre, him⟩

/-- Every finite quartic constituent of a regular canonical tuple has a
radicand that is not a fourth power in the Gaussian integer ring. -/
theorem finiteConstituentRadicand_not_gaussian_fourth_power
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (j : Fin 11) (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
    ¬ ∃ v : 𝓞 GaussianField,
      v ^ 4 = (finiteConstituentRadicand d j : 𝓞 GaussianField) := by
  fin_cases j
  · norm_num at hj
  · simpa [finiteConstituentRadicand] using
      finitePairRadicand_not_gaussian_fourth_power d hreg (quarticPairRepresentative 0)
  · simpa [finiteConstituentRadicand] using
      finitePairRadicand_not_gaussian_fourth_power d hreg (quarticPairRepresentative 1)
  · simpa [finiteConstituentRadicand] using
      finitePairRadicand_not_gaussian_fourth_power d hreg (quarticPairRepresentative 2)
  · simpa [finiteConstituentRadicand] using
      finiteMixedRadicand_not_gaussian_fourth_power d hreg 0
  · simpa [finiteConstituentRadicand] using
      finiteMixedRadicand_not_gaussian_fourth_power d hreg 1
  · simpa [finiteConstituentRadicand] using
      finiteMixedRadicand_not_gaussian_fourth_power d hreg 2
  · simpa [finiteConstituentRadicand] using
      finiteMixedRadicand_not_gaussian_fourth_power d hreg 3
  · simpa [finiteConstituentRadicand] using
      finiteMixedRadicand_not_gaussian_fourth_power d hreg 4
  · simpa [finiteConstituentRadicand] using
      finiteMixedRadicand_not_gaussian_fourth_power d hreg 5
  · norm_num at hj

theorem finiteConstituentRadicand_ne_zero
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (j : Fin 11) (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
    finiteConstituentRadicand d j ≠ 0 := by
  intro hz
  apply finiteConstituentRadicand_not_gaussian_fourth_power d hreg j hj
  refine ⟨0, ?_⟩
  simp [hz]

/-- A regular finite constituent has a nontrivial Gaussian quartic ideal
character on some principal ideal. -/
theorem exists_nontrivial_gaussianQuarticIdealSymbol_finiteConstituent
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (j : Fin 11) (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
    ∃ b : 𝓞 GaussianField,
      ∃ hgood : GaussianQuarticGoodIdeal
          (finiteConstituentRadicand d j : 𝓞 GaussianField)
          (Ideal.span {b}),
        gaussianQuarticIdealSymbol
          (finiteConstituentRadicand d j : 𝓞 GaussianField)
          (Ideal.span {b}) hgood ≠ 1 :=
  exists_nontrivial_gaussianQuarticIdealSymbol_of_not_gaussian_fourth_power
    (finiteConstituentRadicand d j)
    (finiteConstituentRadicand_ne_zero d hreg j hj)
    (finiteConstituentRadicand_not_gaussian_fourth_power d hreg j hj)

private theorem exponentProduct_natAbs_le_cube
    (d : Fin 4 → CanonicalParts) (e : Fin 4 → ℕ)
    (he : ∀ i, e i ≤ 3) :
    (∏ i : Fin 4, ((d i).val : ℤ) ^ e i).natAbs ≤
      (coefficientProduct d) ^ 3 := by
  have hcast : (∏ i : Fin 4, ((d i).val : ℤ) ^ e i) =
      ((∏ i : Fin 4, (d i).val ^ e i : ℕ) : ℤ) := by norm_cast
  rw [hcast]
  simp only [Int.natAbs_natCast]
  calc
    (∏ i : Fin 4, (d i).val ^ e i) ≤
        ∏ i : Fin 4, (d i).val ^ 3 := by
      apply Finset.prod_le_prod
      intro i _
      exact pow_le_pow_right' (d i).property.pos (he i)
    _ = (coefficientProduct d) ^ 3 := by
      simp [coefficientProduct, Finset.prod_pow]

private theorem exponentProduct_dvd_of_coefficient_dvd
    (d : Fin 4 → CanonicalParts) (e : Fin 4 → ℕ)
    (he : ∀ i, 0 < e i) (p : ℕ) (i : Fin 4)
    (hp : p ∣ (d i).val) :
    (p : ℤ) ∣ ∏ t : Fin 4, ((d t).val : ℤ) ^ e t := by
  have hpi : (p : ℤ) ∣ ((d i).val : ℤ) := by exact_mod_cast hp
  have hpow : (p : ℤ) ∣ ((d i).val : ℤ) ^ e i :=
    hpi.trans (dvd_pow_self _ (he i).ne')
  exact hpow.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

theorem finitePairRadicand_natAbs_le_cube
    (d : Fin 4 → CanonicalParts) (j : Fin 4 → Fin 4) :
    (finitePairRadicand d j).natAbs ≤ (coefficientProduct d) ^ 3 := by
  unfold finitePairRadicand
  apply exponentProduct_natAbs_le_cube
  intro i
  split_ifs <;> omega

theorem finiteMixedRadicand_natAbs_le_cube
    (d : Fin 4 → CanonicalParts) (j : Fin 4 → Fin 4) :
    (finiteMixedRadicand d j).natAbs ≤ (coefficientProduct d) ^ 3 := by
  unfold finiteMixedRadicand
  rw [Int.natAbs_neg]
  apply exponentProduct_natAbs_le_cube
  intro i
  split_ifs <;> omega

theorem finitePairRadicand_dvd_of_coefficient_dvd
    (d : Fin 4 → CanonicalParts) (j : Fin 4 → Fin 4)
    (p : ℕ) (i : Fin 4) (hp : p ∣ (d i).val) :
    (p : ℤ) ∣ finitePairRadicand d j := by
  unfold finitePairRadicand
  apply exponentProduct_dvd_of_coefficient_dvd d _ (fun t => ?_) p i hp
  split_ifs <;> omega

theorem finiteMixedRadicand_dvd_of_coefficient_dvd
    (d : Fin 4 → CanonicalParts) (j : Fin 4 → Fin 4)
    (p : ℕ) (i : Fin 4) (hp : p ∣ (d i).val) :
    (p : ℤ) ∣ finiteMixedRadicand d j := by
  unfold finiteMixedRadicand
  apply dvd_neg.mpr
  apply exponentProduct_dvd_of_coefficient_dvd d _ (fun t => ?_) p i hp
  split_ifs <;> omega

/-- Every finite quartic radicand is at most the cube of the coefficient
product in absolute value. -/
theorem finiteConstituentRadicand_natAbs_le_cube
    (d : Fin 4 → CanonicalParts) (j : Fin 11)
    (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
    (finiteConstituentRadicand d j).natAbs ≤
      (coefficientProduct d) ^ 3 := by
  fin_cases j
  · norm_num at hj
  · exact finitePairRadicand_natAbs_le_cube d (quarticPairRepresentative 0)
  · exact finitePairRadicand_natAbs_le_cube d (quarticPairRepresentative 1)
  · exact finitePairRadicand_natAbs_le_cube d (quarticPairRepresentative 2)
  · exact finiteMixedRadicand_natAbs_le_cube d (quarticMixedRepresentative 0)
  · exact finiteMixedRadicand_natAbs_le_cube d (quarticMixedRepresentative 1)
  · exact finiteMixedRadicand_natAbs_le_cube d (quarticMixedRepresentative 2)
  · exact finiteMixedRadicand_natAbs_le_cube d (quarticMixedRepresentative 3)
  · exact finiteMixedRadicand_natAbs_le_cube d (quarticMixedRepresentative 4)
  · exact finiteMixedRadicand_natAbs_le_cube d (quarticMixedRepresentative 5)
  · norm_num at hj

/-- A prime dividing any one of the four coefficients also divides every
finite quartic radicand. -/
theorem finiteConstituentRadicand_dvd_of_coefficient_dvd
    (d : Fin 4 → CanonicalParts) (j : Fin 11)
    (hj : 1 ≤ j.val ∧ j.val ≤ 9)
    (p : ℕ) (i : Fin 4) (hp : p ∣ (d i).val) :
    (p : ℤ) ∣ finiteConstituentRadicand d j := by
  fin_cases j
  · norm_num at hj
  · exact finitePairRadicand_dvd_of_coefficient_dvd d
      (quarticPairRepresentative 0) p i hp
  · exact finitePairRadicand_dvd_of_coefficient_dvd d
      (quarticPairRepresentative 1) p i hp
  · exact finitePairRadicand_dvd_of_coefficient_dvd d
      (quarticPairRepresentative 2) p i hp
  · exact finiteMixedRadicand_dvd_of_coefficient_dvd d
      (quarticMixedRepresentative 0) p i hp
  · exact finiteMixedRadicand_dvd_of_coefficient_dvd d
      (quarticMixedRepresentative 1) p i hp
  · exact finiteMixedRadicand_dvd_of_coefficient_dvd d
      (quarticMixedRepresentative 2) p i hp
  · exact finiteMixedRadicand_dvd_of_coefficient_dvd d
      (quarticMixedRepresentative 3) p i hp
  · exact finiteMixedRadicand_dvd_of_coefficient_dvd d
      (quarticMixedRepresentative 4) p i hp
  · exact finiteMixedRadicand_dvd_of_coefficient_dvd d
      (quarticMixedRepresentative 5) p i hp
  · norm_num at hj

end Erdos940.Quartic
