import Erdos940.Quartic.GaussianHeckeLBridge
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finite prime-exponent vectors for Gaussian ideals

Unique factorization of nonzero Gaussian ideals makes the map from a
finite vector of prime-ideal exponents injective. This is the algebraic
part of reindexing a finite Euler product by ideals.
-/

namespace Erdos940.Quartic.GaussianIdealExponentVectors

open scoped NumberField
open scoped Classical
open nonZeroDivisors
open IsDedekindDomain

noncomputable def idealOfExponents
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (e : S → ℕ) : Ideal (𝓞 GaussianField) :=
  ∏ P : S, P.1.asIdeal ^ e P

private theorem idealOfExponents_coe
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (e : S → ℕ) :
    ((idealOfExponents S e : Ideal (𝓞 GaussianField)) :
      FractionalIdeal (𝓞 GaussianField)⁰ GaussianField) =
      ∏ P : S,
        (P.1.asIdeal : FractionalIdeal (𝓞 GaussianField)⁰ GaussianField) ^ e P := by
  unfold idealOfExponents
  change (FractionalIdeal.coeIdealHom (𝓞 GaussianField)⁰ GaussianField)
      (∏ P : S, P.1.asIdeal ^ e P) = _
  rw [map_prod]
  simp only [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]

theorem count_idealOfExponents
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (e : S → ℕ) (v : HeightOneSpectrum (𝓞 GaussianField)) :
    FractionalIdeal.count GaussianField v
      ((idealOfExponents S e : Ideal (𝓞 GaussianField)) :
        FractionalIdeal (𝓞 GaussianField)⁰ GaussianField) =
      if hv : v ∈ S then (e ⟨v, hv⟩ : ℤ) else 0 := by
  classical
  rw [idealOfExponents_coe]
  rw [FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.count_pow,
      FractionalIdeal.count_maximal, mul_ite, mul_one, mul_zero]
    by_cases hv : v ∈ S
    · have hval : ∀ x : S, ((x : HeightOneSpectrum (𝓞 GaussianField)) = v) ↔
          x = ⟨v, hv⟩ := by
        intro x
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      simp [hval, hv, Finset.sum_ite_eq']
    · simp only [dif_neg hv]
      apply Finset.sum_eq_zero
      intro x hx
      have hne : (x : HeightOneSpectrum (𝓞 GaussianField)) ≠ v := by
        intro heq
        exact hv (heq ▸ x.property)
      simp [hne]
  · intro P _
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.1.ne_bot)

theorem idealOfExponents_injective
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) :
    Function.Injective (idealOfExponents S) := by
  intro e f hef
  funext P
  have h := congrArg
    (fun I : Ideal (𝓞 GaussianField) =>
      FractionalIdeal.count GaussianField P.1
        (I : FractionalIdeal (𝓞 GaussianField)⁰ GaussianField)) hef
  simpa [count_idealOfExponents] using h

/-- Every nonzero Gaussian ideal occurs in some finite exponent vector. -/
theorem exists_idealOfExponents
    (I : Ideal (𝓞 GaussianField)) (hI : I ≠ ⊥) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (e : S → ℕ),
      idealOfExponents S e = I := by
  classical
  let f : HeightOneSpectrum (𝓞 GaussianField) → Ideal (𝓞 GaussianField) :=
    fun P => P.maxPowDividing I
  let hf : Function.HasFiniteMulSupport f := Ideal.hasFiniteMulSupport hI
  let S := hf.toFinset
  let e : S → ℕ := fun P =>
    (Associates.mk P.1.asIdeal).count (Associates.mk I).factors
  refine ⟨S, e, ?_⟩
  calc
    idealOfExponents S e = ∏ P ∈ S, P.maxPowDividing I := by
      unfold idealOfExponents e
      change (∏ P : S, P.1.maxPowDividing I) = ∏ P ∈ S, P.maxPowDividing I
      exact (Finset.prod_subtype S (by simp) (fun P => P.maxPowDividing I)).symm
    _ = ∏ᶠ P : HeightOneSpectrum (𝓞 GaussianField), P.maxPowDividing I := by
      exact (finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Finset.Subset.refl S)).symm
    _ = I := Ideal.finprod_heightOneSpectrum_factorization hI

/-- The prime ideals whose absolute norms do not exceed `n`. -/
noncomputable def primeBox (n : ℕ) :
    Finset (HeightOneSpectrum (𝓞 GaussianField)) :=
  (Set.Finite.preimage HeightOneSpectrum.asIdeal_injective.injOn
    (Ideal.finite_setOfPred_absNorm_le n)).toFinset

theorem mem_primeBox (n : ℕ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    P ∈ primeBox n ↔ P.asIdeal.absNorm ≤ n := by
  simp [primeBox]

theorem norm_le_of_mem_primeBox (n : ℕ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) (hP : P ∈ primeBox n) :
    (Ideal.absNorm P.asIdeal : ℝ) ≤ n := by
  exact_mod_cast (mem_primeBox n P).1 hP

theorem norm_gt_of_not_mem_primeBox (n : ℕ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) (hP : P ∉ primeBox n) :
    (n : ℝ) < Ideal.absNorm P.asIdeal := by
  have h : n < Ideal.absNorm P.asIdeal := Nat.lt_of_not_ge (by
    intro hle
    exact hP ((mem_primeBox n P).2 hle))
  exact_mod_cast h

theorem primeBox_mono : Monotone primeBox := by
  intro m n hmn P hP
  exact (mem_primeBox n P).2 ((mem_primeBox m P).1 hP |>.trans hmn)

theorem exists_mem_primeBox
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    ∃ n, P ∈ primeBox n := by
  exact ⟨P.asIdeal.absNorm, (mem_primeBox _ P).2 le_rfl⟩

theorem idealOfExponents_subset
    {S T : Finset (HeightOneSpectrum (𝓞 GaussianField))}
    (hST : S ⊆ T) (e : S → ℕ) :
    idealOfExponents T (fun P =>
      if hP : (P : HeightOneSpectrum (𝓞 GaussianField)) ∈ S then e ⟨P, hP⟩ else 0) =
      idealOfExponents S e := by
  classical
  let F : HeightOneSpectrum (𝓞 GaussianField) → Ideal (𝓞 GaussianField) :=
    fun P => P.asIdeal ^ (if hP : P ∈ S then e ⟨P, hP⟩ else 0)
  have hT : idealOfExponents T (fun P =>
        if hP : (P : HeightOneSpectrum (𝓞 GaussianField)) ∈ S then e ⟨P, hP⟩ else 0) =
      ∏ P ∈ T, F P := by
    rw [← Finset.prod_coe_sort T F]
    rfl
  have hS : idealOfExponents S e = ∏ P ∈ S, F P := by
    rw [← Finset.prod_coe_sort S F]
    simp [idealOfExponents, F]
  rw [hT, hS]
  exact (Finset.prod_subset hST (by
    intro P hPT hPS
    simp [F, hPS])).symm

/-- Nonzero ideals represented by a finite prime set and bounded exponents. -/
noncomputable def idealBox
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ) :
    Finset (Ideal (𝓞 GaussianField)) :=
  Finset.univ.image (fun e : S → Fin (N + 1) =>
    idealOfExponents S (fun P => (e P).val))

theorem idealOfExponents_ne_bot
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (e : S → ℕ) :
    idealOfExponents S e ≠ ⊥ := by
  unfold idealOfExponents
  exact Finset.prod_ne_zero_iff.mpr (fun P _ => pow_ne_zero _ P.1.ne_bot)

theorem bot_not_mem_idealBox
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ) :
    ⊥ ∉ idealBox S N := by
  intro h
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
  exact idealOfExponents_ne_bot S (fun P => (e P).val) he

theorem mem_idealBox_iff
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) (N : ℕ)
    (I : Ideal (𝓞 GaussianField)) :
    I ∈ idealBox S N ↔
      ∃ e : S → ℕ, (∀ P, e P ≤ N) ∧ idealOfExponents S e = I := by
  classical
  constructor
  · intro h
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨fun P => (e P).val, fun P => Nat.lt_succ_iff.mp (e P).isLt, rfl⟩
  · rintro ⟨e, he, rfl⟩
    let e' : S → Fin (N + 1) := fun P => ⟨e P, Nat.lt_succ_iff.mpr (he P)⟩
    exact Finset.mem_image.mpr ⟨e', Finset.mem_univ _, rfl⟩

theorem idealBox_mono_cutoff
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) :
    Monotone (idealBox S) := by
  intro M N hMN I hI
  obtain ⟨e, he, rfl⟩ := (mem_idealBox_iff S M I).mp hI
  exact (mem_idealBox_iff S N _).mpr ⟨e, fun P => (he P).trans hMN, rfl⟩

theorem idealBox_mono_primes
    {S T : Finset (HeightOneSpectrum (𝓞 GaussianField))}
    (hST : S ⊆ T) (N : ℕ) : idealBox S N ⊆ idealBox T N := by
  intro I hI
  obtain ⟨e, he, rfl⟩ := (mem_idealBox_iff S N I).mp hI
  let f : T → ℕ := fun P =>
    if hP : (P : HeightOneSpectrum (𝓞 GaussianField)) ∈ S then e ⟨P, hP⟩ else 0
  apply (mem_idealBox_iff T N _).mpr
  refine ⟨f, ?_, ?_⟩
  · intro P
    by_cases hP : (P : HeightOneSpectrum (𝓞 GaussianField)) ∈ S
    · simpa [f, hP] using he ⟨P, hP⟩
    · simp [f, hP]
  · exact idealOfExponents_subset hST e

/-- Every nonzero ideal eventually occurs in a norm-indexed prime box with
some finite exponent cutoff. -/
theorem exists_mem_primeBox_idealBox
    (I : Ideal (𝓞 GaussianField)) (hI : I ≠ ⊥) :
    ∃ n N, I ∈ idealBox (primeBox n) N := by
  classical
  obtain ⟨S, e, rfl⟩ := exists_idealOfExponents I hI
  let n := S.sup (fun P => P.asIdeal.absNorm)
  let N := Finset.univ.sup e
  have hS : S ⊆ primeBox n := by
    intro P hP
    exact (mem_primeBox n P).2
      (Finset.le_sup (f := fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        P.asIdeal.absNorm) hP)
  have he : ∀ P : S, e P ≤ N := by
    intro P
    exact Finset.le_sup (Finset.mem_univ P)
  refine ⟨n, N, ?_⟩
  exact idealBox_mono_primes hS N
    ((mem_idealBox_iff S N _).mpr ⟨e, he, rfl⟩)

theorem idealBox_primeBox_mono
    {m n M N : ℕ} (hmn : m ≤ n) (hMN : M ≤ N) :
    idealBox (primeBox m) M ⊆ idealBox (primeBox n) N := by
  exact (idealBox_mono_primes (primeBox_mono hmn) M).trans
    (idealBox_mono_cutoff (primeBox n) hMN)

/-- Any monotone exponent cutoff at least as large as the prime-norm
cutoff gives an exhaustive sequence of finite ideal boxes. -/
theorem exists_mem_idealBox_diagonal
    (cutoff : ℕ → ℕ) (hcutoff : ∀ n, n ≤ cutoff n)
    (I : Ideal (𝓞 GaussianField)) (hI : I ≠ ⊥) :
    ∃ n, I ∈ idealBox (primeBox n) (cutoff n) := by
  obtain ⟨m, M, hIbox⟩ := exists_mem_primeBox_idealBox I hI
  refine ⟨max m M, ?_⟩
  exact idealBox_primeBox_mono (le_max_left m M)
    ((le_max_right m M).trans (hcutoff (max m M))) hIbox

end Erdos940.Quartic.GaussianIdealExponentVectors
