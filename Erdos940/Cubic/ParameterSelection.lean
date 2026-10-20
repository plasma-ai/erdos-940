module

public import Erdos940.Cubic.Parts
public import Erdos940.Cubic.PrimeSupply
public import Erdos940.Cubic.Sieve
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The finite choices in the three-cube-full argument

The choices in Section 5 of Beyer and de Ryke are made in this order:
a threshold `T`, a finite family `D` of canonical parts with a small
weighted tail, a finite batch `Q` of suitable primes, and—after the
modulus has been determined—a larger finite family `E` with a small
unweighted tail. These lemmas isolate the existence of those choices
from the subsequent local and lattice-point estimates.
-/

@[expose] public section

namespace Erdos940

open Filter Topology
open scoped Classical

/-- The omitted `H`-weight after retaining a finite family of parts. -/
noncomputable def weightedPartTail (D : Finset CanonicalParts) : ℝ :=
  ∑' d : {d : CanonicalParts // d ∉ D},
    (3 : ℝ) ^ d.val.val.primeFactors.card *
      (d.val.val : ℝ) ^ (-(1 / 3 : ℝ))

/-- The omitted `W`-weight after retaining a finite family of parts. -/
noncomputable def unweightedPartTail (E : Finset CanonicalParts) : ℝ :=
  ∑' d : {d : CanonicalParts // d ∉ E},
    (d.val.val : ℝ) ^ (-(1 / 3 : ℝ))

/-- The subtype form of the `W`-tail agrees with the indicator form used
by the sieve bound. -/
theorem tailPartWeight_eq_unweightedPartTail (E : Finset CanonicalParts) :
    tailPartWeight E = unweightedPartTail E := by
  classical
  unfold tailPartWeight unweightedPartTail partWeight
  calc
    (∑' d : CanonicalParts,
        if d ∉ E then (d.val : ℝ) ^ (-(1 / 3 : ℝ)) else 0) =
        ∑' d : CanonicalParts,
          Set.indicator {d : CanonicalParts | d ∉ E}
            (fun d => (d.val : ℝ) ^ (-(1 / 3 : ℝ))) d := by
      apply tsum_congr
      intro d
      simp [Set.indicator_apply]
    _ = ∑' d : {d : CanonicalParts // d ∉ E},
          (d.val.val : ℝ) ^ (-(1 / 3 : ℝ)) :=
      (tsum_subtype (s := {d : CanonicalParts | d ∉ E})
        (f := fun d : CanonicalParts => (d.val : ℝ) ^ (-(1 / 3 : ℝ)))).symm

/-- A finite part family whose weighted tail is as small as required. -/
theorem exists_parts_with_small_weighted_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Finset CanonicalParts, weightedPartTail D < ε := by
  simpa only [weightedPartTail] using canonicalPart_weighted_tail ε hε

/-- After `D` is chosen, a larger finite family can make the unweighted
tail arbitrarily small. The modulus is not needed for this existence
statement; it enters only through the requested tolerance. -/
theorem exists_larger_parts_with_small_unweighted_tail
    (D : Finset CanonicalParts) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset CanonicalParts, D ⊆ E ∧ unweightedPartTail E < ε := by
  have htend := tendsto_tsum_compl_atTop_zero
    (fun d : CanonicalParts => (d.val : ℝ) ^ (-(1 / 3 : ℝ)))
  have htail : ∀ᶠ E : Finset CanonicalParts in atTop,
      unweightedPartTail E < ε :=
    (tendsto_order.1 htend).2 ε hε
  obtain ⟨E, hDE, hsmall⟩ := ((eventually_ge_atTop D).and htail).exists
  exact ⟨E, hDE, hsmall⟩

private theorem scaled_small_tail {A ε t : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (ht : t < ε / (A + 1)) :
    A * t < ε := by
  have hden : 0 < A + 1 := by linarith
  have hne : A + 1 ≠ 0 := hden.ne'
  have hmul : A * t ≤ A * (ε / (A + 1)) :=
    mul_le_mul_of_nonneg_left ht.le hA
  have hbound : A * (ε / (A + 1)) = ε - ε / (A + 1) := by
    field_simp [hne]
    ring
  calc
    A * t ≤ A * (ε / (A + 1)) := hmul
    _ = ε - ε / (A + 1) := hbound
    _ < ε := sub_lt_self ε (div_pos hε hden)

/-- Any nonnegative factor can be absorbed into the weighted-tail choice. -/
theorem exists_parts_with_scaled_weighted_tail
    (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ D : Finset CanonicalParts, A * weightedPartTail D < ε := by
  have hden : 0 < A + 1 := by linarith
  obtain ⟨D, hD⟩ :=
    exists_parts_with_small_weighted_tail (ε / (A + 1)) (div_pos hε hden)
  exact ⟨D, scaled_small_tail hA hε hD⟩

/-- Once the modulus is known, enlarge `D` so the unweighted tail fits
any prescribed multiple of that modulus. -/
theorem exists_larger_parts_with_scaled_unweighted_tail
    (D : Finset CanonicalParts) (A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ E : Finset CanonicalParts,
      D ⊆ E ∧ A * unweightedPartTail E < ε := by
  have hden : 0 < A + 1 := by linarith
  obtain ⟨E, hDE, hE⟩ :=
    exists_larger_parts_with_small_unweighted_tail D
      (ε / (A + 1)) (div_pos hε hden)
  exact ⟨E, hDE, scaled_small_tail hA hε hE⟩

/-- The specific `32 M` margin used for the third contribution in
`Assembly`; `C` is the remaining nonnegative coefficient of the tail. -/
theorem exists_larger_parts_with_assembly_slack
    (D : Finset CanonicalParts) (M : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ E : Finset CanonicalParts,
      D ⊆ E ∧ 32 * (M : ℝ) * C * unweightedPartTail E < 1 := by
  have hA : 0 ≤ (32 : ℝ) * M * C := by positivity
  exact exists_larger_parts_with_scaled_unweighted_tail D
    (32 * (M : ℝ) * C) 1 hA (by norm_num)

/-- The exact tail inequality consumed by the scaled sieve estimate: the
parts outside `E` contribute less than one unit after multiplication by
`32 M` and the global quadratic weight. -/
theorem exists_larger_parts_for_sieve_estimate
    (D : Finset CanonicalParts) (M : ℕ) :
    ∃ E : Finset CanonicalParts, D ⊆ E ∧
      (32 * (M : ℝ)) *
        (3 * totalPartWeight ^ 2 * tailPartWeight E) < 1 := by
  obtain ⟨E, hDE, hsmall⟩ := exists_larger_parts_with_assembly_slack
    D M (3 * totalPartWeight ^ 2) (by positivity)
  refine ⟨E, hDE, ?_⟩
  calc
    (32 * (M : ℝ)) * (3 * totalPartWeight ^ 2 * tailPartWeight E) =
        32 * (M : ℝ) * (3 * totalPartWeight ^ 2) *
          unweightedPartTail E := by
      rw [tailPartWeight_eq_unweightedPartTail]
      ring
    _ < 1 := hsmall

/-- Exponential decay permits the initial threshold to be chosen before
the finite sets or modulus. The coefficient may be any real number. -/
theorem exists_decay_threshold (C δ : ℝ) (hδ : 0 < δ) :
    ∃ T : ℝ, 0 ≤ T ∧ C * Real.exp (-(2 * T)) < δ := by
  have hlim : Tendsto (fun T : ℝ => C * Real.exp (-(2 * T))) atTop (𝓝 0) := by
    have hexp : Tendsto (fun T : ℝ => Real.exp ((-2) * T)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
    convert hexp.const_mul C using 1 <;> simp
  have hsmall : ∀ᶠ T : ℝ in atTop, C * Real.exp (-(2 * T)) < δ :=
    (tendsto_order.1 hlim).2 δ hδ
  obtain ⟨T, hT, hsmallT⟩ := ((eventually_ge_atTop (0 : ℝ)).and hsmall).exists
  exact ⟨T, hT, hsmallT⟩

/-- The natural-number values of the canonical parts in `D`, used by the
splitting-field prime-supply theorem. -/
def partValues (D : Finset CanonicalParts) : Finset ℕ := D.image Subtype.val

theorem partValues_pos (D : Finset CanonicalParts) :
    ∀ d ∈ partValues D, 0 < d := by
  intro d hd
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
  exact e.property.pos

/-- Choose a small weighted tail and then a finite prime batch. Each chosen
prime makes every part in `D` a nonzero cube. -/
theorem exists_parts_and_good_prime_batch
    (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ (D : Finset CanonicalParts) (Q : Finset ℕ),
      weightedPartTail D < ε ∧
      (∀ q ∈ Q, GoodPrime (partValues D) q) ∧
      T ≤ ∑ q ∈ Q, (1 : ℝ) / q ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 := by
  obtain ⟨D, hD⟩ := exists_parts_with_small_weighted_tail ε hε
  obtain ⟨Q, hQ, hsumLower, hsumUpper⟩ :=
    finite_goodPrime_batch (partValues D) (partValues_pos D) T hT
  exact ⟨D, Q, hD, hQ, hsumLower, hsumUpper⟩

/-- A combined form with the core decay slack `1/64`, leaving room under
the `1/32` budget used for each contribution in `Assembly`. -/
theorem exists_threshold_parts_and_good_primes
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ (T : ℝ) (D : Finset CanonicalParts) (Q : Finset ℕ),
      0 ≤ T ∧ C * Real.exp (-(2 * T)) < (1 / 64 : ℝ) ∧
      weightedPartTail D < ε ∧
      (∀ q ∈ Q, GoodPrime (partValues D) q) ∧
      T ≤ ∑ q ∈ Q, (1 : ℝ) / q ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 := by
  obtain ⟨T, hT, hdecay⟩ := exists_decay_threshold C (1 / 64) (by norm_num)
  obtain ⟨D, Q, hD, hQ, hsumLower, hsumUpper⟩ :=
    exists_parts_and_good_prime_batch T ε hT hε
  exact ⟨T, D, Q, hT, hdecay, hD, hQ, hsumLower, hsumUpper⟩

/-- The complete order of choices. The desired weighted-tail tolerance may
depend on `T`; after the prime batch determines a modulus `M`, the larger
family `E` can be chosen with the exact sieve margin. -/
theorem exists_section5_choices
    (C : ℝ) (weightedTolerance : ℝ → ℝ)
    (hTolerance : ∀ T, 0 ≤ T → 0 < weightedTolerance T) :
    ∃ (T : ℝ) (D : Finset CanonicalParts) (Q : Finset ℕ),
      0 ≤ T ∧ C * Real.exp (-(2 * T)) < (1 / 64 : ℝ) ∧
      weightedPartTail D < weightedTolerance T ∧
      (∀ q ∈ Q, GoodPrime (partValues D) q) ∧
      T ≤ ∑ q ∈ Q, (1 : ℝ) / q ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 ∧
      ∀ M : ℕ, ∃ E : Finset CanonicalParts, D ⊆ E ∧
        (32 * (M : ℝ)) *
          (3 * totalPartWeight ^ 2 * tailPartWeight E) < 1 := by
  obtain ⟨T, hT, hdecay⟩ := exists_decay_threshold C (1 / 64) (by norm_num)
  obtain ⟨D, Q, hD, hQ, hsumLower, hsumUpper⟩ :=
    exists_parts_and_good_prime_batch T (weightedTolerance T) hT
      (hTolerance T hT)
  exact ⟨T, D, Q, hT, hdecay, hD, hQ, hsumLower, hsumUpper,
    fun M => exists_larger_parts_for_sieve_estimate D M⟩

end Erdos940
