import Erdos940.Quartic.GaussianPrimeIdealFibers
import Erdos940.Quartic.GaussianIdealExponentVectors
import Erdos940.Quartic.ProgressionBuilder
import Erdos940.Quartic.GaussianFiniteConstituentTrace
import Erdos940.Quartic.GaussianPrimeIdealNorm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The degree-two correction in Gaussian prime sums

An inert rational prime contributes one Gaussian prime ideal of norm its
square. The total reciprocal-norm contribution from such primes is bounded
by an absolute constant, uniformly in the cutoff.
-/

namespace Erdos940.Quartic

open scoped NumberField
open scoped Classical
open NumberField IsDedekindDomain

theorem gaussianPrime_absNorm_eq_basePrime_of_degreeOne
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hdegree : gaussianDegreeOne P) :
    Ideal.absNorm P.asIdeal = (gaussianBasePrime P).val := by
  classical
  have h := gaussianIdealNorm_eq_absNorm P
  have hr : ((gaussianBasePrime P).val : ℝ) =
      (Ideal.absNorm P.asIdeal : ℝ) := by
    simpa [gaussianIdealNorm, hdegree] using h
  exact_mod_cast hr.symm

theorem gaussianPrime_absNorm_mem_quarticBasePrimes_of_degreeOne
    (B : ℕ) (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : P ∈ GaussianIdealExponentVectors.primeBox B)
    (hdegree : gaussianDegreeOne P)
    (hnotTwo : Ideal.absNorm P.asIdeal ≠ 2) :
    Ideal.absNorm P.asIdeal ∈ quarticBasePrimes B := by
  have hnorm := gaussianPrime_absNorm_eq_basePrime_of_degreeOne P hdegree
  have hp : (Ideal.absNorm P.asIdeal).Prime := by
    rw [hnorm]
    exact (gaussianBasePrime P).property
  have hle : Ideal.absNorm P.asIdeal ≤ B :=
    (GaussianIdealExponentVectors.mem_primeBox B P).1 hP
  have hthree : 3 ≤ Ideal.absNorm P.asIdeal := by
    have htwo := hp.two_le
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hthree, hle⟩, hp⟩

/-- A norm omitted from the good base-prime sum comes only from a degree-two
ideal, the ramified norm `2`, or the chosen bad-prime predicate. -/
theorem gaussianPrime_omittedGoodBase_classification
    (B : ℕ) (good : ℕ → Prop)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : P ∈ GaussianIdealExponentVectors.primeBox B)
    (homit : Ideal.absNorm P.asIdeal ∉
      (quarticBasePrimes B).filter good) :
    ¬ gaussianDegreeOne P ∨ Ideal.absNorm P.asIdeal = 2 ∨
      ¬ good (Ideal.absNorm P.asIdeal) := by
  classical
  by_cases hdegree : gaussianDegreeOne P
  · right
    by_cases htwo : Ideal.absNorm P.asIdeal = 2
    · exact Or.inl htwo
    · right
      intro hgood
      exact homit (Finset.mem_filter.mpr
        ⟨gaussianPrime_absNorm_mem_quarticBasePrimes_of_degreeOne
            B P hP hdegree htwo, hgood⟩)
  · exact Or.inl hdegree

theorem gaussianDegreeTwoReciprocalSum_le
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField))) :
    (∑ P ∈ F.filter (fun P => ¬ gaussianDegreeOne P),
      (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ)) ≤
      reciprocalSquareConstant := by
  classical
  let T := F.filter (fun P => ¬ gaussianDegreeOne P)
  have hterm (P : HeightOneSpectrum (𝓞 GaussianField))
      (hP : P ∈ T) :
      (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) =
        (((gaussianBasePrime P).val : ℝ) ^ 2)⁻¹ := by
    have hnot : ¬ gaussianDegreeOne P := (Finset.mem_filter.mp hP).2
    rw [← gaussianIdealNorm_eq_absNorm P]
    simp [gaussianIdealNorm, hnot]
  calc
    (∑ P ∈ F.filter (fun P => ¬ gaussianDegreeOne P),
      (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ)) =
        ∑ P ∈ T, (((gaussianBasePrime P).val : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact hterm P hP
    _ ≤ ∑ p ∈ T.image gaussianBasePrime,
        ((p.val : ℝ) ^ 2)⁻¹ := by
      have h := sum_over_prime_fibers_le T gaussianBasePrime
        (fun p => ((p.val : ℝ) ^ 2)⁻¹) 1
        (fun _ => by positivity)
        (gaussianDegreeTwo_fiber_card_le_one F)
      simpa using h
    _ ≤ reciprocalSquareConstant := by
      have hinj : Function.Injective (fun p : Nat.Primes => p.val) :=
        Subtype.val_injective
      rw [← Finset.sum_image (s := T.image gaussianBasePrime)
        (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
        (fun p _ q _ h => hinj h)]
      simpa only [one_div] using finite_reciprocalSquares_le _

theorem gaussianDegreeTwoWeightedSum_abs_le
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ)
    (hc : ∀ P ∈ F, |c P| ≤ 1) :
    |∑ P ∈ F.filter (fun P => ¬ gaussianDegreeOne P),
        c P / (Ideal.absNorm P.asIdeal : ℝ)| ≤
      reciprocalSquareConstant := by
  calc
    |∑ P ∈ F.filter (fun P => ¬ gaussianDegreeOne P),
        c P / (Ideal.absNorm P.asIdeal : ℝ)| ≤
        ∑ P ∈ F.filter (fun P => ¬ gaussianDegreeOne P),
          |c P / (Ideal.absNorm P.asIdeal : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ P ∈ F.filter (fun P => ¬ gaussianDegreeOne P),
          (1 : ℝ) / (Ideal.absNorm P.asIdeal : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hn : 0 < (Ideal.absNorm P.asIdeal : ℝ) := by
        exact_mod_cast (zero_lt_one.trans
          (NumberField.HeightOneSpectrum.one_lt_absNorm P))
      rw [abs_div, abs_of_pos hn]
      exact div_le_div_of_nonneg_right
        (hc P (Finset.mem_filter.mp hP).1) hn.le
    _ ≤ reciprocalSquareConstant := gaussianDegreeTwoReciprocalSum_le F

/-- Reindex a finite sum of ideal weights by the integer absolute norms of
its prime ideals. The outer norm set need not contain every norm in `F`. -/
theorem gaussianPrimeNormFiberSum_eq_filter
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (T : Finset ℕ)
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ) :
    (∑ p ∈ T,
      (∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal = p), c P) / (p : ℝ)) =
      ∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal ∈ T),
        c P / (Ideal.absNorm P.asIdeal : ℝ) := by
  classical
  calc
    (∑ p ∈ T,
      (∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal = p), c P) / (p : ℝ)) =
        ∑ p ∈ T,
          ∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal = p),
            c P / (Ideal.absNorm P.asIdeal : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro P hP
      rw [(Finset.mem_filter.mp hP).2]
    _ = ∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal ∈ T),
          c P / (Ideal.absNorm P.asIdeal : ℝ) := by
      exact Finset.sum_fiberwise_eq_sum_filter F T
        (fun P => Ideal.absNorm P.asIdeal)
        (fun P => c P / (Ideal.absNorm P.asIdeal : ℝ))

theorem primeBox_normFiber_eq_splitFiber
    (B q : ℕ) [Fact q.Prime] (hqB : q ≤ B)
    (ρ : GaussianInt →+* ZMod q) (π : GaussianInt)
    (hπnorm : π.norm = q)
    (hker : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z) :
    (GaussianIdealExponentVectors.primeBox B).filter
        (fun P => Ideal.absNorm P.asIdeal = q) =
      gaussianSplitNormPrimeFiber q ρ π hπnorm hker := by
  ext P
  rw [Finset.mem_filter, GaussianIdealExponentVectors.mem_primeBox,
    mem_gaussianSplitNormPrimeFiber_iff]
  constructor
  · exact And.right
  · intro hnorm
    exact ⟨hnorm ▸ hqB, hnorm⟩

theorem gaussianPrimeNormFiber_empty_of_mod_four_three
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (q : ℕ) (hq : q % 4 = 3) :
    F.filter (fun P => Ideal.absNorm P.asIdeal = q) = ∅ := by
  ext P
  constructor
  · intro hP
    exfalso
    have hnorm := (Finset.mem_filter.mp hP).2
    exact (gaussian_prime_ideal_absNorm_mod_four_ne_three P)
      (by rw [hnorm, hq])
  · intro hP
    simp at hP

/-- Removing the ramified and deliberately bad degree-one fibers changes a
Gaussian prime sum by at most the degree-two reciprocal-norm constant. -/
theorem gaussianPrime_goodBaseSum_le_full_add_constant
    (B : ℕ) (good : ℕ → Prop)
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ)
    (hc : ∀ P ∈ GaussianIdealExponentVectors.primeBox B, |c P| ≤ 1)
    (hzero : ∀ P ∈ GaussianIdealExponentVectors.primeBox B,
      gaussianDegreeOne P →
      (Ideal.absNorm P.asIdeal = 2 ∨ ¬ good (Ideal.absNorm P.asIdeal)) →
      c P = 0) :
    (∑ P ∈ (GaussianIdealExponentVectors.primeBox B).filter
        (fun P => Ideal.absNorm P.asIdeal ∈ (quarticBasePrimes B).filter good),
      c P / (Ideal.absNorm P.asIdeal : ℝ)) ≤
      (∑ P ∈ GaussianIdealExponentVectors.primeBox B,
        c P / (Ideal.absNorm P.asIdeal : ℝ)) +
        reciprocalSquareConstant := by
  classical
  let F := GaussianIdealExponentVectors.primeBox B
  let T := (quarticBasePrimes B).filter good
  let f : HeightOneSpectrum (𝓞 GaussianField) → ℝ :=
    fun P => c P / (Ideal.absNorm P.asIdeal : ℝ)
  let O := F.filter (fun P => Ideal.absNorm P.asIdeal ∉ T)
  have hsplit : (∑ P ∈ F, f P) =
      (∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal ∈ T), f P) +
        (∑ P ∈ O, f P) := by
    simpa [O] using (Finset.sum_filter_add_sum_filter_not F
      (fun P => Ideal.absNorm P.asIdeal ∈ T) f).symm
  have hzeroSum : (∑ P ∈ O.filter gaussianDegreeOne, f P) = 0 := by
    apply Finset.sum_eq_zero
    intro P hP
    have hPO : P ∈ O := (Finset.mem_filter.mp hP).1
    have hdegree : gaussianDegreeOne P := (Finset.mem_filter.mp hP).2
    have hF : P ∈ F := (Finset.mem_filter.mp hPO).1
    have homit : Ideal.absNorm P.asIdeal ∉ T :=
      (Finset.mem_filter.mp hPO).2
    have hcase := gaussianPrime_omittedGoodBase_classification
      B good P hF homit
    have hbad : Ideal.absNorm P.asIdeal = 2 ∨
        ¬good (Ideal.absNorm P.asIdeal) :=
      hcase.resolve_left (not_not_intro hdegree)
    simp [f, hzero P hF hdegree hbad]
  have hO : |∑ P ∈ O, f P| ≤ reciprocalSquareConstant := by
    have hs : (∑ P ∈ O, f P) =
        ∑ P ∈ O.filter (fun P => ¬gaussianDegreeOne P), f P := by
      rw [← Finset.sum_filter_add_sum_filter_not O gaussianDegreeOne f]
      simp [hzeroSum]
    rw [hs]
    exact gaussianDegreeTwoWeightedSum_abs_le O c
      (by intro P hPO; exact hc P (Finset.mem_filter.mp hPO).1)
  have hOlower : -reciprocalSquareConstant ≤ ∑ P ∈ O, f P :=
    (neg_le_of_abs_le hO)
  dsimp [f] at hsplit hOlower ⊢
  linarith

/-- Apply the norm-fiber identity and the uniformly bounded omitted-fiber
correction to a rational-prime constituent. -/
theorem rationalBasePrimeSum_le_gaussianPrimeSum_add_constant
    (B : ℕ) (good : ℕ → Prop)
    (b : ℕ → ℝ)
    (c : HeightOneSpectrum (𝓞 GaussianField) → ℝ)
    (hc : ∀ P ∈ GaussianIdealExponentVectors.primeBox B, |c P| ≤ 1)
    (hzero : ∀ P ∈ GaussianIdealExponentVectors.primeBox B,
      gaussianDegreeOne P →
      (Ideal.absNorm P.asIdeal = 2 ∨ ¬ good (Ideal.absNorm P.asIdeal)) →
      c P = 0)
    (hlocal : ∀ p ∈ (quarticBasePrimes B).filter good,
      b p = ∑ P ∈ (GaussianIdealExponentVectors.primeBox B).filter
        (fun P => Ideal.absNorm P.asIdeal = p), c P) :
    (∑ p ∈ (quarticBasePrimes B).filter good, b p / (p : ℝ)) ≤
      (∑ P ∈ GaussianIdealExponentVectors.primeBox B,
        c P / (Ideal.absNorm P.asIdeal : ℝ)) +
        reciprocalSquareConstant := by
  calc
    (∑ p ∈ (quarticBasePrimes B).filter good, b p / (p : ℝ)) =
        ∑ p ∈ (quarticBasePrimes B).filter good,
          (∑ P ∈ (GaussianIdealExponentVectors.primeBox B).filter
            (fun P => Ideal.absNorm P.asIdeal = p), c P) / (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hlocal p hp]
    _ = ∑ P ∈ (GaussianIdealExponentVectors.primeBox B).filter
          (fun P => Ideal.absNorm P.asIdeal ∈ (quarticBasePrimes B).filter good),
          c P / (Ideal.absNorm P.asIdeal : ℝ) :=
      gaussianPrimeNormFiberSum_eq_filter _ _ c
    _ ≤ _ := gaussianPrime_goodBaseSum_le_full_add_constant B good c hc hzero

end Erdos940.Quartic
