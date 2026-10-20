import Erdos940.Quartic.GaussianIdealLBound
import Erdos940.Quartic.GaussianIdealExponentVectors
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Gaussian ideal Dirichlet series as a sum over ideals

This is the norm-fibre reindexing needed before applying unique
factorization of ideals to the quartic Euler product.
-/

namespace Erdos940.Quartic.GaussianIdealEulerIdentity

open scoped NumberField
open scoped Topology
open IsDedekindDomain
open Filter
open Asymptotics
open nonZeroDivisors
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianIdealExponentVectors

/-- A term of the Dirichlet series indexed by ideals rather than norms. -/
noncomputable def idealTerm (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (s : ℂ)
    (I : Ideal (𝓞 GaussianField)) : ℂ :=
  if I = ⊥ then 0 else
    quarticIdealWeight R ι I / (I.absNorm : ℂ) ^ s

private theorem goodIdeal_top (R : 𝓞 GaussianField) :
    GaussianQuarticGoodIdeal R ⊤ := by
  refine ⟨by simp, ?_⟩
  intro P hP
  have hunit : IsUnit P.asIdeal := isUnit_of_dvd_one (by simpa using hP)
  exact (P.isPrime.ne_top (Ideal.isUnit_iff.mp hunit)).elim

private theorem idealWeight_top (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) : quarticIdealWeight R ι ⊤ = 1 := by
  have hnorm : ‖quarticIdealWeight R ι ⊤‖ = 1 := by
    simp only [quarticIdealWeight, dif_pos (goodIdeal_top R)]
    exact norm_gaussianQuarticComplexValue ι _
  have hmul := GaussianIdealLBound.quarticIdealCoeff_weight_mul R ι ⊤ ⊤
  have hmul' : quarticIdealWeight R ι ⊤ =
      quarticIdealWeight R ι ⊤ * quarticIdealWeight R ι ⊤ := by
    simpa using hmul
  have hnonzero : quarticIdealWeight R ι ⊤ ≠ 0 := by
    intro hz
    simp [hz] at hnorm
  have hcancel : quarticIdealWeight R ι ⊤ * 1 =
      quarticIdealWeight R ι ⊤ * quarticIdealWeight R ι ⊤ := by
    simpa using hmul'
  exact (mul_left_cancel₀ hnonzero hcancel).symm

theorem quarticIdealWeight_top (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) : quarticIdealWeight R ι ⊤ = 1 :=
  idealWeight_top R ι

theorem idealTerm_top (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (s : ℂ) :
    idealTerm R ι s ⊤ = 1 := by
  simp [idealTerm, idealWeight_top]

/-- The ideal-indexed summand is completely multiplicative. -/
theorem idealTerm_mul (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (s : ℂ)
    (I J : Ideal (𝓞 GaussianField)) :
    idealTerm R ι s (I * J) =
      idealTerm R ι s I * idealTerm R ι s J := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealTerm]
  by_cases hJ : J = ⊥
  · subst J
    simp [idealTerm]
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [idealTerm, if_neg hI, if_neg hJ, if_neg hIJ]
  rw [GaussianIdealLBound.quarticIdealCoeff_weight_mul,
    map_mul Ideal.absNorm, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- Unique factorization turns each nonzero ideal summand into the finite
product of its prime-power summands. -/
theorem idealTerm_eq_finprod_prime_powers
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (s : ℂ)
    (I : Ideal (𝓞 GaussianField)) (hI : I ≠ ⊥) :
    idealTerm R ι s I =
      ∏ᶠ P : HeightOneSpectrum (𝓞 GaussianField),
        idealTerm R ι s (P.maxPowDividing I) := by
  let F : Ideal (𝓞 GaussianField) →* ℂ :=
    { toFun := idealTerm R ι s
      map_one' := by simpa only [Ideal.one_eq_top] using idealTerm_top R ι s
      map_mul' := idealTerm_mul R ι s }
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  exact F.map_finprod (Ideal.hasFiniteMulSupport hI)

/-- The number of Gaussian ideals in a fixed positive norm shell. -/
noncomputable def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 GaussianField) // I.absNorm = n}

private theorem partial_idealCount_eq (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, idealCount k) =
      Nat.card {I : (Ideal (𝓞 GaussianField))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 GaussianField)) ≤ n} := by
  unfold idealCount
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 GaussianField) // I.absNorm = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- Gaussian ideals have a linearly bounded cumulative norm count. -/
theorem partial_idealCount_isBigO :
    (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, idealCount k : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have ht := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ GaussianField).comp
    tendsto_natCast_atTop_atTop
  have hO :
      (fun n : ℕ => (Nat.card {I : (Ideal (𝓞 GaussianField))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 GaussianField)) ≤ n} : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    refine ht.congr' ?_
    filter_upwards [] with n
    simp [Function.comp_apply]
  simpa only [Real.rpow_one, ← Nat.cast_sum, partial_idealCount_eq] using hO

/-- Absolute convergence of the Gaussian ideal-count Dirichlet series. -/
theorem idealCount_LSeriesSummable (σ : ℝ) (hσ : 1 < σ) :
    LSeriesSummable (fun n => (idealCount n : ℂ)) (σ : ℂ) := by
  apply LSeriesSummable_of_sum_norm_bigO
    (r := 1) (s := (σ : ℂ))
  · simpa only [Complex.norm_natCast, Real.rpow_one] using partial_idealCount_isBigO
  · norm_num
  · simpa using hσ

private noncomputable def idealMajorant (σ : ℝ)
    (I : Ideal (𝓞 GaussianField)) : ℝ :=
  if I = ⊥ then 0 else 1 / (I.absNorm : ℝ) ^ σ

private theorem sum_idealMajorant_normShell (σ : ℝ) (n : ℕ) :
    (∑ I ∈ gaussianAllIdealNormShell n, idealMajorant σ I) =
      if n = 0 then 0 else (idealCount n : ℝ) / (n : ℝ) ^ σ := by
  classical
  by_cases hn : n = 0
  · subst n
    have hs0 : gaussianAllIdealNormShell 0 = {⊥} := by
      ext I
      simp [mem_gaussianAllIdealNormShell_iff, Ideal.absNorm_eq_zero_iff]
    simp [hs0, idealMajorant]
  · rw [if_neg hn]
    have hpoint (I : Ideal (𝓞 GaussianField))
        (hI : I ∈ gaussianAllIdealNormShell n) :
        idealMajorant σ I = 1 / (n : ℝ) ^ σ := by
      have hnorm := (mem_gaussianAllIdealNormShell_iff n I).mp hI
      have hI0 : I ≠ ⊥ := by
        intro h
        exact hn (by simpa [h] using hnorm.symm)
      simp [idealMajorant, hI0, hnorm]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_const, nsmul_eq_mul]
    have hcard : (gaussianAllIdealNormShell n).card = idealCount n := by
      haveI : Finite ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _) :=
        (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      letI : Fintype ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _) :=
        Fintype.ofFinite _
      change ({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _).toFinset.card =
        Nat.card ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _)
      rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    rw [hcard]
    ring

private theorem summable_idealCount_real (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => if n = 0 then 0 else
      (idealCount n : ℝ) / (n : ℝ) ^ σ) := by
  have h := (idealCount_LSeriesSummable σ hσ).norm
  simpa [LSeriesSummable, LSeries.norm_term_eq] using h

/-- The ideal-norm majorant is summable for every real exponent above one. -/
theorem summable_idealMajorant (σ : ℝ) (hσ : 1 < σ) :
    Summable (idealMajorant σ) := by
  classical
  rw [summable_partition (fun I => by unfold idealMajorant; split_ifs <;> positivity)
    (s := fun n : ℕ => {I : Ideal (𝓞 GaussianField) | I.absNorm = n})
    (by intro I; exact ⟨I.absNorm, by simp, by simp_all⟩)]
  constructor
  · intro n
    haveI : Finite ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _) :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    change Summable (fun I : ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _) =>
      idealMajorant σ I)
    exact Summable.of_finite
  · have hfib (n : ℕ) :
        (∑' I : {I : Ideal (𝓞 GaussianField) | I.absNorm = n},
          idealMajorant σ I) =
        if n = 0 then 0 else (idealCount n : ℝ) / (n : ℝ) ^ σ := by
      haveI : Finite ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _) :=
        (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      letI : Fintype ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _) :=
        Fintype.ofFinite _
      change (∑' I : ↥({I : Ideal (𝓞 GaussianField) | I.absNorm = n} : Set _),
        idealMajorant σ I) = _
      rw [tsum_fintype]
      rw [Finset.sum_set_coe]
      exact sum_idealMajorant_normShell σ n
    simpa only [hfib] using summable_idealCount_real σ hσ

/-- The Dirichlet summand for an arbitrary weight on Gaussian ideals. -/
noncomputable def weightedIdealTerm
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (I : Ideal (𝓞 GaussianField)) : ℂ :=
  if I = ⊥ then 0 else w I / (I.absNorm : ℂ) ^ s

theorem weightedIdealTerm_top
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hw : w ⊤ = 1) : weightedIdealTerm w s ⊤ = 1 := by
  simp [weightedIdealTerm, hw]

theorem weightedIdealTerm_mul
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (I J : Ideal (𝓞 GaussianField)) :
    weightedIdealTerm w s (I * J) =
      weightedIdealTerm w s I * weightedIdealTerm w s J := by
  by_cases hI : I = ⊥
  · subst I
    simp [weightedIdealTerm]
  by_cases hJ : J = ⊥
  · subst J
    simp [weightedIdealTerm]
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [weightedIdealTerm, if_neg hI, if_neg hJ, if_neg hIJ]
  rw [hwmul, map_mul Ideal.absNorm, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

theorem weightedIdealTerm_pow
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (I : Ideal (𝓞 GaussianField)) (n : ℕ) :
    weightedIdealTerm w s (I ^ n) =
      weightedIdealTerm w s I ^ n := by
  induction n with
  | zero => simpa only [pow_zero, Ideal.one_eq_top] using
      weightedIdealTerm_top w s hwone
  | succ n ih =>
      rw [pow_succ, weightedIdealTerm_mul w s hwmul, ih, pow_succ]

theorem weightedIdealTerm_eq_finprod_prime_powers
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (I : Ideal (𝓞 GaussianField)) (hI : I ≠ ⊥) :
    weightedIdealTerm w s I =
      ∏ᶠ P : HeightOneSpectrum (𝓞 GaussianField),
        weightedIdealTerm w s (P.maxPowDividing I) := by
  let F : Ideal (𝓞 GaussianField) →* ℂ :=
    { toFun := weightedIdealTerm w s
      map_one' := by simpa only [Ideal.one_eq_top] using
        weightedIdealTerm_top w s hwone
      map_mul' := weightedIdealTerm_mul w s hwmul }
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  exact F.map_finprod (Ideal.hasFiniteMulSupport hI)

/-- The coefficient of an individual ideal is the product of its
prime-local geometric monomials. -/
theorem weightedIdealTerm_eq_finprod_prime_monomials
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (I : Ideal (𝓞 GaussianField)) (hI : I ≠ ⊥) :
    weightedIdealTerm w s I =
      ∏ᶠ P : HeightOneSpectrum (𝓞 GaussianField),
        weightedIdealTerm w s P.asIdeal ^
          (Associates.mk P.asIdeal).count (Associates.mk I).factors := by
  rw [weightedIdealTerm_eq_finprod_prime_powers w s hwone hwmul I hI]
  congr 1
  funext P
  simp [HeightOneSpectrum.maxPowDividing,
    weightedIdealTerm_pow w s hwone hwmul]

/-- Finite prime support and finite exponent cutoffs expand without any
analytic interchange. The summands are the monomials that correspond to
ideals with all prime factors in `S` and exponents below `N`. -/
theorem finite_prime_product_expansion
    [DecidableEq (HeightOneSpectrum (𝓞 GaussianField))]
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ) :
    (∏ P ∈ S, ∑ e ∈ Finset.range N,
      weightedIdealTerm w s P.asIdeal ^ e) =
      ∑ e ∈ S.pi (fun _ => Finset.range N),
        ∏ P ∈ S.attach,
          weightedIdealTerm w s P.1.asIdeal ^ e P.1 P.2 := by
  classical
  exact Finset.prod_sum S (fun _ => Finset.range N)
    (fun P e => weightedIdealTerm w s P.asIdeal ^ e)

/-- The monomial selected by a finite vector of prime exponents is the
Dirichlet-series term of the associated ideal. -/
theorem product_prime_monomial_eq_weightedIdealTerm
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (e : S → ℕ) :
    (∏ P : S, weightedIdealTerm w s P.1.asIdeal ^ e P) =
      weightedIdealTerm w s (idealOfExponents S e) := by
  let F : Ideal (𝓞 GaussianField) →* ℂ :=
    { toFun := weightedIdealTerm w s
      map_one' := by simpa only [Ideal.one_eq_top] using
        weightedIdealTerm_top w s hwone
      map_mul' := weightedIdealTerm_mul w s hwmul }
  change (∏ P : S, F P.1.asIdeal ^ e P) = F (idealOfExponents S e)
  rw [idealOfExponents, map_prod]
  simp only [map_pow]

/-- A finite Euler product with finite local cutoffs is exactly the
Dirichlet sum over the finite box of exponent vectors. -/
theorem finite_prime_product_eq_ideal_box_sum
    [DecidableEq (HeightOneSpectrum (𝓞 GaussianField))]
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ) :
    (∏ P ∈ S, ∑ e ∈ Finset.range N,
      weightedIdealTerm w s (P.asIdeal ^ e)) =
      ∑ I ∈ (S.pi (fun _ => Finset.range N)).image
        (fun e => idealOfExponents S (fun P => e P.1 P.2)),
        weightedIdealTerm w s I := by
  classical
  simp_rw [weightedIdealTerm_pow w s hwone hwmul]
  rw [finite_prime_product_expansion]
  rw [Finset.sum_image (by
    intro e he f hf h
    have hef : (fun P : S => e P.1 P.2) = (fun P : S => f P.1 P.2) :=
      idealOfExponents_injective S h
    funext P hP
    exact congrFun hef ⟨P, hP⟩)]
  apply Finset.sum_congr rfl
  intro e he
  exact product_prime_monomial_eq_weightedIdealTerm w s hwone hwmul S
    (fun P => e P.1 P.2)

/-- The dependent-function enumeration in `Finset.prod_sum` agrees with
the finite ideal box indexed by subtype-valued exponent vectors. -/
theorem image_pi_eq_idealBox
    [DecidableEq (HeightOneSpectrum (𝓞 GaussianField))]
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ) :
    (S.pi (fun _ => Finset.range (N + 1))).image
      (fun e => idealOfExponents S (fun P => e P.1 P.2)) =
      idealBox S N := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hI
    apply (mem_idealBox_iff S N _).mpr
    refine ⟨fun P => e P.1 P.2, ?_, rfl⟩
    intro P
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp
      ((Finset.mem_pi.mp he) P.1 P.2))
  · intro hI
    obtain ⟨e, he, rfl⟩ := (mem_idealBox_iff S N I).mp hI
    let f : ∀ P, P ∈ S → ℕ := fun P hP => e ⟨P, hP⟩
    apply Finset.mem_image.mpr
    refine ⟨f, ?_, rfl⟩
    exact Finset.mem_pi.mpr (by
      intro P hP
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (he ⟨P, hP⟩)))

theorem finite_prime_product_eq_sum_idealBox
    [DecidableEq (HeightOneSpectrum (𝓞 GaussianField))]
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ) :
    (∏ P ∈ S, ∑ e ∈ Finset.range (N + 1),
      weightedIdealTerm w s (P.asIdeal ^ e)) =
      ∑ I ∈ idealBox S N, weightedIdealTerm w s I := by
  rw [finite_prime_product_eq_ideal_box_sum w s hwone hwmul S (N + 1),
    image_pi_eq_idealBox]

/-- Unit-bounded ideal weights have absolutely summable ideal-indexed
Dirichlet series for real exponents greater than one. -/
theorem summable_weightedIdealTerm
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) :
    Summable (weightedIdealTerm w (σ : ℂ)) := by
  apply (summable_idealMajorant σ hσ).of_norm_bounded
  intro I
  by_cases hI : I = ⊥
  · simp [weightedIdealTerm, idealMajorant, hI]
  have hn : 0 < I.absNorm :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [weightedIdealTerm, idealMajorant, if_neg hI, norm_div]
  rw [Complex.norm_natCast_cpow_of_pos hn]
  exact div_le_div_of_nonneg_right (hw I) (by positivity)

theorem norm_weightedIdealTerm_prime_lt_one
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    ‖weightedIdealTerm w (σ : ℂ) P.asIdeal‖ < 1 := by
  have hn0 : 0 < P.asIdeal.absNorm := by
    exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)
  have hn1 : P.asIdeal.absNorm ≠ 1 := by
    intro h
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hn : 1 < P.asIdeal.absNorm := by omega
  have hpow : 1 < (P.asIdeal.absNorm : ℝ) ^ σ :=
    Real.one_lt_rpow (by exact_mod_cast hn) (by linarith)
  have hbound : ‖weightedIdealTerm w (σ : ℂ) P.asIdeal‖ ≤
      1 / (P.asIdeal.absNorm : ℝ) ^ σ := by
    have hP : P.asIdeal ≠ ⊥ := P.ne_bot
    simp only [weightedIdealTerm, if_neg hP, norm_div]
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    exact div_le_div_of_nonneg_right (hw P.asIdeal) (by positivity)
  exact hbound.trans_lt ((div_lt_iff₀ (by positivity :
    0 < (P.asIdeal.absNorm : ℝ) ^ σ)).2 (by simpa using hpow))

theorem weightedIdeal_local_geometric_series
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (σ : ℝ) (hσ : 1 < σ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹ =
      ∑' e : ℕ, weightedIdealTerm w (σ : ℂ) (P.asIdeal ^ e) := by
  simp_rw [weightedIdealTerm_pow w _ hwone hwmul]
  exact (tsum_geometric_of_norm_lt_one
    (norm_weightedIdealTerm_prime_lt_one w hw σ hσ P)).symm

/-- The exponential logarithm in the analytic comparison is precisely
the infinite product of local Euler factors. -/
theorem exp_tsum_prime_log_eq_tprod_local_factor
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (σ : ℝ) (hσ : 1 < σ) :
    Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
      -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)) =
      ∏' P : HeightOneSpectrum (𝓞 GaussianField),
        (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹ := by
  have hsum : Summable (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
      weightedIdealTerm w (σ : ℂ) P.asIdeal) :=
    (summable_weightedIdealTerm w hw σ hσ).comp_injective
      HeightOneSpectrum.asIdeal_injective
  have hlog := hsum.clog_one_sub.neg
  have h := hlog.hasSum.cexp.tprod_eq
  have hz (P : HeightOneSpectrum (𝓞 GaussianField)) :
      (1 : ℂ) - weightedIdealTerm w (σ : ℂ) P.asIdeal ≠ 0 := by
    intro hzero
    have heq : weightedIdealTerm w (σ : ℂ) P.asIdeal = 1 := by
      exact sub_eq_zero.mp hzero |>.symm
    have hlt := norm_weightedIdealTerm_prime_lt_one w hw σ hσ P
    simp [heq] at hlt
  have heq :
      (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        (Complex.exp (Complex.log
          (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)))⁻¹) =
      (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹) := by
    funext P
    rw [Complex.exp_log (hz P)]
  simpa only [Function.comp_apply, Complex.exp_neg, heq] using h.symm

/-- The local inverse factors have the stated infinite product. -/
theorem hasProd_local_factor
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (σ : ℝ) (hσ : 1 < σ) :
    HasProd (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
      (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹)
      (Complex.exp (∑' P : HeightOneSpectrum (𝓞 GaussianField),
        -Complex.log (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal))) := by
  have hsum : Summable (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
      weightedIdealTerm w (σ : ℂ) P.asIdeal) :=
    (summable_weightedIdealTerm w hw σ hσ).comp_injective
      HeightOneSpectrum.asIdeal_injective
  have h := (hsum.clog_one_sub.neg).hasSum.cexp
  convert h using 1
  funext P
  have hz : (1 : ℂ) - weightedIdealTerm w (σ : ℂ) P.asIdeal ≠ 0 := by
    intro hzero
    have heq : weightedIdealTerm w (σ : ℂ) P.asIdeal = 1 :=
      (sub_eq_zero.mp hzero).symm
    have hlt := norm_weightedIdealTerm_prime_lt_one w hw σ hσ P
    simp [heq] at hlt
  simp [Complex.exp_neg, Complex.exp_log hz]

/-- Norm-indexed coefficients for a general Gaussian ideal weight. -/
noncomputable def weightedIdealCoeff
    (w : Ideal (𝓞 GaussianField) → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ∑ I ∈ gaussianAllIdealNormShell n, w I

theorem weightedIdealTerm_eq_idealTerm
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (s : ℂ)
    (I : Ideal (𝓞 GaussianField)) :
    weightedIdealTerm (quarticIdealWeight R ι) s I = idealTerm R ι s I := rfl

theorem weightedIdealCoeff_eq_quarticIdealCoeff
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (n : ℕ) :
    weightedIdealCoeff (quarticIdealWeight R ι) n =
      quarticIdealCoeff R ι n := rfl

/-- Absolute convergence of the quartic ideal Dirichlet series in the
half-plane of absolute convergence. -/
theorem summable_idealTerm (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (σ : ℝ) (hσ : 1 < σ) :
    Summable (idealTerm R ι (σ : ℂ)) := by
  apply (summable_idealMajorant σ hσ).of_norm_bounded
  intro I
  by_cases hI : I = ⊥
  · simp [idealTerm, idealMajorant, hI]
  have hn : 0 < I.absNorm :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [idealTerm, idealMajorant, if_neg hI, norm_div]
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have hd : 0 ≤ (I.absNorm : ℝ) ^ σ := by positivity
  calc
    ‖quarticIdealWeight R ι I‖ / (I.absNorm : ℝ) ^ σ ≤
        1 / (I.absNorm : ℝ) ^ σ := by
      exact div_le_div_of_nonneg_right (norm_quarticIdealWeight_le_one R ι I) hd

/-- The norm-fibre sum is precisely the corresponding `LSeries` term. -/
theorem sum_idealTerm_normShell (R : 𝓞 GaussianField)
    (ι : GaussianField →+* ℂ) (s : ℂ) (n : ℕ) :
    (∑ I ∈ gaussianAllIdealNormShell n, idealTerm R ι s I) =
      LSeries.term (quarticIdealCoeff R ι) s n := by
  classical
  by_cases hn : n = 0
  · subst n
    have hs0 : gaussianAllIdealNormShell 0 = {⊥} := by
      ext I
      simp [mem_gaussianAllIdealNormShell_iff, Ideal.absNorm_eq_zero_iff]
    simp [hs0, idealTerm, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [quarticIdealCoeff, if_neg hn]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro I hI
    have hI0 : I ≠ ⊥ := by
      intro h
      have : I.absNorm = 0 := by simpa [h] using Ideal.absNorm_bot
      exact hn ((mem_gaussianAllIdealNormShell_iff n I).mp hI ▸ this)
    simp [idealTerm, hI0, (mem_gaussianAllIdealNormShell_iff n I).mp hI]

/-- Absolute convergence of the ideal series allows norm-fibre regrouping. -/
theorem quarticIdealLSeries_eq_tsum_idealTerm
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (s : ℂ)
    (hsum : Summable (idealTerm R ι s)) :
    LSeries (quarticIdealCoeff R ι) s =
      ∑' I : Ideal (𝓞 GaussianField), idealTerm R ι s I := by
  classical
  rw [← (hsum.hasSum.tsum_fiberwise
    (fun I : Ideal (𝓞 GaussianField) => I.absNorm)).tsum_eq]
  simp only [LSeries]
  apply tsum_congr
  intro n
  have hfin : Set.Finite ((fun I : Ideal (𝓞 GaussianField) => I.absNorm) ⁻¹' {n}) := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (Ideal.finite_setOfPred_absNorm_eq n :
        Set.Finite {I : Ideal (𝓞 GaussianField) | I.absNorm = n})
  haveI : Finite ((fun I : Ideal (𝓞 GaussianField) => I.absNorm) ⁻¹' {n}) :=
    hfin.to_subtype
  letI : Fintype ((fun I : Ideal (𝓞 GaussianField) => I.absNorm) ⁻¹' {n}) :=
    Fintype.ofFinite _
  rw [tsum_fintype]
  rw [← sum_idealTerm_normShell R ι s n]
  rw [Finset.sum_set_coe]
  congr 1

/-- The norm shell of an arbitrary ideal weight is its weighted
Dirichlet-series coefficient. -/
theorem sum_weightedIdealTerm_normShell
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ) (n : ℕ) :
    (∑ I ∈ gaussianAllIdealNormShell n, weightedIdealTerm w s I) =
      LSeries.term (weightedIdealCoeff w) s n := by
  classical
  by_cases hn : n = 0
  · subst n
    have hs0 : gaussianAllIdealNormShell 0 = {⊥} := by
      ext I
      simp [mem_gaussianAllIdealNormShell_iff, Ideal.absNorm_eq_zero_iff]
    simp [hs0, weightedIdealTerm, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [weightedIdealCoeff, if_neg hn]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro I hI
    have hI0 : I ≠ ⊥ := by
      intro h
      have : I.absNorm = 0 := by simpa [h] using Ideal.absNorm_bot
      exact hn ((mem_gaussianAllIdealNormShell_iff n I).mp hI ▸ this)
    simp [weightedIdealTerm, hI0,
      (mem_gaussianAllIdealNormShell_iff n I).mp hI]

/-- Norm-fibre regrouping for a general Gaussian ideal weight. -/
theorem weightedIdealLSeries_eq_tsum_weightedIdealTerm
    (w : Ideal (𝓞 GaussianField) → ℂ) (s : ℂ)
    (hsum : Summable (weightedIdealTerm w s)) :
    LSeries (weightedIdealCoeff w) s =
      ∑' I : Ideal (𝓞 GaussianField), weightedIdealTerm w s I := by
  classical
  rw [← (hsum.hasSum.tsum_fiberwise
    (fun I : Ideal (𝓞 GaussianField) => I.absNorm)).tsum_eq]
  simp only [LSeries]
  apply tsum_congr
  intro n
  have hfin : Set.Finite ((fun I : Ideal (𝓞 GaussianField) => I.absNorm) ⁻¹' {n}) := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (Ideal.finite_setOfPred_absNorm_eq n :
        Set.Finite {I : Ideal (𝓞 GaussianField) | I.absNorm = n})
  haveI : Finite ((fun I : Ideal (𝓞 GaussianField) => I.absNorm) ⁻¹' {n}) :=
    hfin.to_subtype
  letI : Fintype ((fun I : Ideal (𝓞 GaussianField) => I.absNorm) ⁻¹' {n}) :=
    Fintype.ofFinite _
  rw [tsum_fintype]
  rw [← sum_weightedIdealTerm_normShell w s n]
  rw [Finset.sum_set_coe]
  congr 1

theorem weightedIdealLSeries_eq_tsum_of_one_lt
    (w : Ideal (𝓞 GaussianField) → ℂ) (hw : ∀ I, ‖w I‖ ≤ 1)
    (σ : ℝ) (hσ : 1 < σ) :
    LSeries (weightedIdealCoeff w) (σ : ℂ) =
      ∑' I : Ideal (𝓞 GaussianField), weightedIdealTerm w (σ : ℂ) I :=
  weightedIdealLSeries_eq_tsum_weightedIdealTerm w _
    (summable_weightedIdealTerm w hw σ hσ)

/-- An absolutely summable series is the limit of sums over any nested
finite family that eventually contains each index. This is the analytic
limit principle for expanding ideal Euler products in finite boxes. -/
theorem tendsto_sum_exhaustive_boxes
    {β : Type*} (f : β → ℂ) (hf : Summable f)
    (box : ℕ → Finset β) (hmono : Monotone box)
    (hexhaustive : ∀ b, ∃ n, b ∈ box n) :
    Filter.Tendsto (fun n => ∑ b ∈ box n, f b)
      Filter.atTop (𝓝 (∑' b, f b)) := by
  classical
  have hcofinal : ∀ u : Finset β, ∃ n, u ⊆ box n := by
    intro u
    induction u using Finset.induction with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert b u hbu ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm⟩ := hexhaustive b
        refine ⟨max n m, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxu
        · exact (hmono (le_max_right n m)) hm
        · exact (hmono (le_max_left n m)) (hn hxu)
  have hbox : Filter.Tendsto box Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro u
    obtain ⟨n, hn⟩ := hcofinal u
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact hn.trans (hmono hm)
  have hsum : Filter.Tendsto (fun u : Finset β => ∑ b ∈ u, f b)
      Filter.atTop (𝓝 (∑' b, f b)) := hf.hasSum
  exact hsum.comp hbox

theorem tendsto_prod_exhaustive_boxes
    {β : Type*} (f : β → ℂ) (a : ℂ) (hf : HasProd f a)
    (box : ℕ → Finset β) (hmono : Monotone box)
    (hexhaustive : ∀ b, ∃ n, b ∈ box n) :
    Filter.Tendsto (fun n => ∏ b ∈ box n, f b)
      Filter.atTop (𝓝 a) := by
  classical
  have hcofinal : ∀ u : Finset β, ∃ n, u ⊆ box n := by
    intro u
    induction u using Finset.induction with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | @insert b u hbu ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm⟩ := hexhaustive b
        refine ⟨max n m, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxu
        · exact (hmono (le_max_right n m)) hm
        · exact (hmono (le_max_left n m)) (hn hxu)
  have hbox : Filter.Tendsto box Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro u
    obtain ⟨n, hn⟩ := hcofinal u
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact hn.trans (hmono hm)
  exact hf.comp hbox

/-- Choose increasingly large cutoffs so a sequence of pointwise
approximations is asymptotically exact along the diagonal. -/
theorem exists_monotone_diagonal_cutoffs
    (f : ℕ → ℕ → ℂ) (g : ℕ → ℂ)
    (hf : ∀ n, Filter.Tendsto (f n) Filter.atTop (𝓝 (g n))) :
    ∃ N : ℕ → ℕ, Monotone N ∧ (∀ n, n ≤ N n) ∧
      Filter.Tendsto (fun n => dist (f n (N n)) (g n))
        Filter.atTop (𝓝 0) := by
  classical
  have hex (n : ℕ) : ∃ K : ℕ, ∀ k ≥ K,
      dist (f n k) (g n) < 1 / ((n : ℝ) + 1) := by
    exact (Metric.tendsto_atTop.mp (hf n)) _ (by positivity)
  let K : ℕ → ℕ := fun n => Classical.choose (hex n)
  have hK (n : ℕ) (k : ℕ) (hk : K n ≤ k) :
      dist (f n k) (g n) < 1 / ((n : ℝ) + 1) :=
    Classical.choose_spec (hex n) k hk
  let N : ℕ → ℕ := Nat.rec (K 0) (fun n a => max a (K (n + 1)) + 1)
  have hNstep (n : ℕ) : N n ≤ N (n + 1) := by
    change N n ≤ max (N n) (K (n + 1)) + 1
    omega
  have hNmono : Monotone N := monotone_nat_of_le_succ hNstep
  have hNlower (n : ℕ) : n ≤ N n := by
    induction n with
    | zero => omega
    | succ n ih =>
        change n + 1 ≤ max (N n) (K (n + 1)) + 1
        omega
  have hNK (n : ℕ) : K n ≤ N n := by
    induction n with
    | zero => exact le_of_eq (by rfl)
    | succ n ih =>
        change K (n + 1) ≤ max (N n) (K (n + 1)) + 1
        omega
  refine ⟨N, hNmono, hNlower, ?_⟩
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      1 / ((n : ℝ) + 1) < ε := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (eventually_lt_nhds hε)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨n₀, ?_⟩
  intro n hn
  simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg :
    0 ≤ dist (f n (N n)) (g n))] using
    lt_trans (hK n (N n) (hNK n)) (hn₀ n hn)

end Erdos940.Quartic.GaussianIdealEulerIdentity
