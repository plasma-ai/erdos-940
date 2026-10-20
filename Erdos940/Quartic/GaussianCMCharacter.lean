import Erdos940.Quartic.GaussianCMParity
import Erdos940.Quartic.GaussianCMSign
import Erdos940.Quartic.GaussianIdealLatticeSeries
import Erdos940.Quartic.GaussianIdealLBound
import Erdos940.Quartic.GaussianAnyConductorPeriodicity

/-!
# The infinity-type-two Gaussian CM ideal character

An ideal of odd norm has a Gaussian generator with odd real part and even
imaginary part, unique up to sign. Squaring that generator and dividing by
the ideal norm defines a unitary ideal character of infinity type two.
-/

namespace Erdos940.Quartic.GaussianCMCharacter

open scoped NumberField
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianHeckeLBridge
open Erdos940.Quartic.GaussianCoefficientLBound
open Erdos940.Quartic.GaussianLBound

/-- A choice of Gaussian generator for each ideal, via the PID structure. -/
noncomputable def gaussianIdealGenerator (I : Ideal (𝓞 GaussianField)) : GaussianInt :=
  gaussianFourthIntegerRingEquiv.symm (Submodule.IsPrincipal.generator I)

theorem gaussianPrincipalIdeal_gaussianIdealGenerator
    (I : Ideal (𝓞 GaussianField)) :
    gaussianPrincipalIdeal (gaussianIdealGenerator I) = I := by
  simpa [gaussianPrincipalIdeal, gaussianIdealGenerator] using
    (Ideal.span_singleton_generator I)

theorem gaussianIdealGenerator_norm
    (I : Ideal (𝓞 GaussianField)) :
    (gaussianIdealGenerator I).norm.natAbs = I.absNorm := by
  rw [← absNorm_gaussianPrincipalIdeal,
    gaussianPrincipalIdeal_gaussianIdealGenerator]

/-- The parity of an ideal's absolute norm transfers to its chosen Gaussian
generator. -/
theorem gaussianIdealGenerator_odd_norm
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    ((gaussianIdealGenerator I).norm : ZMod 2) = 1 := by
  have hnat := congrArg (fun n : ℕ => (n : ZMod 2))
    (gaussianIdealGenerator_norm I)
  have hcast := congrArg (fun n : ℤ => (n : ZMod 2))
    (GaussianInt.abs_natCast_norm (gaussianIdealGenerator I))
  simpa [hodd] using hcast.symm.trans (by simpa [hodd] using hnat)

/-- Every ideal of odd norm has an odd-real, even-imaginary Gaussian
generator. -/
theorem exists_gaussian_normalized_generator
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    ∃ z : GaussianInt,
      gaussianPrincipalIdeal z = I ∧ GaussianParityNormalized z := by
  let g := gaussianIdealGenerator I
  obtain ⟨u, hu, hnorm⟩ := gaussian_odd_norm_normalize g
    (gaussianIdealGenerator_odd_norm I hodd)
  refine ⟨g * u, ?_, hnorm⟩
  have hspan : gaussianPrincipalIdeal (g * u) = gaussianPrincipalIdeal g := by
    unfold gaussianPrincipalIdeal
    rw [map_mul]
    exact Ideal.span_singleton_mul_right_unit
      (IsUnit.map gaussianFourthIntegerRingEquiv.toRingHom hu) _
  exact hspan.trans (gaussianPrincipalIdeal_gaussianIdealGenerator I)

/-- A parity-normalized generator of an odd-norm ideal. -/
noncomputable def normalizedGaussianIdealGenerator
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) : GaussianInt :=
  Classical.choose (exists_gaussian_normalized_generator I hodd)

theorem normalizedGaussianIdealGenerator_ideal
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    gaussianPrincipalIdeal (normalizedGaussianIdealGenerator I hodd) = I :=
  (Classical.choose_spec (exists_gaussian_normalized_generator I hodd)).1

theorem normalizedGaussianIdealGenerator_parity
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    GaussianParityNormalized (normalizedGaussianIdealGenerator I hodd) :=
  (Classical.choose_spec (exists_gaussian_normalized_generator I hodd)).2

/-- The square of a normalized generator does not depend on its choice. -/
theorem normalizedGaussianIdealGenerator_sq_eq
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1)
    (z : GaussianInt)
    (hideal : gaussianPrincipalIdeal z = I)
    (hparity : GaussianParityNormalized z) :
    (normalizedGaussianIdealGenerator I hodd) ^ 2 = z ^ 2 := by
  obtain ⟨u, hu⟩ :=
    (gaussianPrincipalIdeal_eq_iff_associated z
      (normalizedGaussianIdealGenerator I hodd)).mp
      ((normalizedGaussianIdealGenerator_ideal I hodd).trans hideal.symm)
  exact gaussianParityNormalized_associated_square_eq z
    (normalizedGaussianIdealGenerator I hodd) u u.isUnit hu.symm
    hparity (normalizedGaussianIdealGenerator_parity I hodd)

theorem gaussianPrincipalIdeal_mul (z w : GaussianInt) :
    gaussianPrincipalIdeal (z * w) =
      gaussianPrincipalIdeal z * gaussianPrincipalIdeal w := by
  simp [gaussianPrincipalIdeal, map_mul,
    Ideal.span_singleton_mul_span_singleton]

theorem gaussianPrincipalIdeal_mul_i (z : GaussianInt) :
    gaussianPrincipalIdeal (z * Zsqrtd.sqrtd) =
      gaussianPrincipalIdeal z := by
  unfold gaussianPrincipalIdeal
  rw [map_mul]
  have hiunit : IsUnit (Zsqrtd.sqrtd : GaussianInt) := by
    apply (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) _).mp
    norm_num [Zsqrtd.norm]
  exact Ideal.span_singleton_mul_right_unit
    (IsUnit.map gaussianFourthIntegerRingEquiv.toRingHom hiunit) _

theorem normalizedGaussianIdealGenerator_sq_mul
    (I J : Ideal (𝓞 GaussianField))
    (hI : (I.absNorm : ZMod 2) = 1)
    (hJ : (J.absNorm : ZMod 2) = 1)
    (hIJ : ((I * J).absNorm : ZMod 2) = 1) :
    (normalizedGaussianIdealGenerator (I * J) hIJ) ^ 2 =
      (normalizedGaussianIdealGenerator I hI) ^ 2 *
        (normalizedGaussianIdealGenerator J hJ) ^ 2 := by
  let zI := normalizedGaussianIdealGenerator I hI
  let zJ := normalizedGaussianIdealGenerator J hJ
  have hspan : gaussianPrincipalIdeal (zI * zJ) = I * J := by
    rw [gaussianPrincipalIdeal_mul,
      normalizedGaussianIdealGenerator_ideal,
      normalizedGaussianIdealGenerator_ideal]
  have hparity : GaussianParityNormalized (zI * zJ) :=
    gaussianParityNormalized_mul zI zJ
      (normalizedGaussianIdealGenerator_parity I hI)
      (normalizedGaussianIdealGenerator_parity J hJ)
  rw [← mul_pow]
  exact normalizedGaussianIdealGenerator_sq_eq (I * J) hIJ
    (zI * zJ) hspan hparity

/-- The primitive infinity-type-two Gaussian CM character, extended by zero
on ideals above two. -/
noncomputable def gaussianNuIdealWeight
    (I : Ideal (𝓞 GaussianField)) : ℂ :=
  if hodd : (I.absNorm : ZMod 2) = 1 then
    ((normalizedGaussianIdealGenerator I hodd : ℂ) ^ 2) / (I.absNorm : ℂ)
  else 0

theorem gaussianNuIdealWeight_of_odd
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    gaussianNuIdealWeight I =
      ((normalizedGaussianIdealGenerator I hodd : ℂ) ^ 2) / (I.absNorm : ℂ) := by
  simp [gaussianNuIdealWeight, hodd]

theorem gaussianNuIdealWeight_of_even
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) ≠ 1) :
    gaussianNuIdealWeight I = 0 := by
  simp [gaussianNuIdealWeight, hodd]

private theorem zmod_two_eq_zero_of_ne_one (x : ZMod 2) (hx : x ≠ 1) :
    x = 0 := by
  have hcase : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  exact (hcase x).resolve_right hx

/-- The normalized CM weight is multiplicative on all integral ideals. -/
theorem gaussianNuIdealWeight_mul
    (I J : Ideal (𝓞 GaussianField)) :
    gaussianNuIdealWeight (I * J) =
      gaussianNuIdealWeight I * gaussianNuIdealWeight J := by
  have hnorm : ((I * J).absNorm : ZMod 2) =
      (I.absNorm : ZMod 2) * (J.absNorm : ZMod 2) := by
    simp [map_mul]
  by_cases hI : (I.absNorm : ZMod 2) = 1
  · by_cases hJ : (J.absNorm : ZMod 2) = 1
    · have hIJ : ((I * J).absNorm : ZMod 2) = 1 := by
        rw [hnorm, hI, hJ, one_mul]
      rw [gaussianNuIdealWeight_of_odd _ hIJ,
        gaussianNuIdealWeight_of_odd _ hI,
        gaussianNuIdealWeight_of_odd _ hJ]
      rw [← map_pow, normalizedGaussianIdealGenerator_sq_mul I J hI hJ hIJ,
        map_mul]
      simp only [map_mul, map_pow, Nat.cast_mul]
      ring
    · have hJ0 := zmod_two_eq_zero_of_ne_one _ hJ
      have hIJ : ((I * J).absNorm : ZMod 2) ≠ 1 := by
        rw [hnorm, hJ0, mul_zero]
        exact zero_ne_one
      simp [gaussianNuIdealWeight_of_even _ hJ,
        gaussianNuIdealWeight_of_even _ hIJ]
  · have hI0 := zmod_two_eq_zero_of_ne_one _ hI
    have hIJ : ((I * J).absNorm : ZMod 2) ≠ 1 := by
      rw [hnorm, hI0, zero_mul]
      exact zero_ne_one
    simp [gaussianNuIdealWeight_of_even _ hI,
      gaussianNuIdealWeight_of_even _ hIJ]

theorem normalizedGaussianIdealGenerator_complex_normSq
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    Complex.normSq (normalizedGaussianIdealGenerator I hodd : ℂ) =
      (I.absNorm : ℝ) := by
  let z := normalizedGaussianIdealGenerator I hodd
  have hznorm : z.norm.natAbs = I.absNorm := by
    rw [← absNorm_gaussianPrincipalIdeal,
      normalizedGaussianIdealGenerator_ideal]
  have hnat : (z.norm : ℝ) = (I.absNorm : ℝ) := by
    rw [← GaussianInt.abs_natCast_norm z]
    exact_mod_cast hznorm
  have hcomplex : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) =
      (I.absNorm : ℂ) := by
    rw [← GaussianInt.intCast_complex_norm]
    exact_mod_cast hnat
  exact_mod_cast hcomplex

theorem norm_gaussianNuIdealWeight_eq_one_of_odd
    (I : Ideal (𝓞 GaussianField))
    (hodd : (I.absNorm : ZMod 2) = 1) :
    ‖gaussianNuIdealWeight I‖ = 1 := by
  have hnonzero : I.absNorm ≠ 0 := by
    intro hzero
    simp [hzero] at hodd
  have hpos : (0 : ℝ) < I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero hnonzero
  rw [gaussianNuIdealWeight_of_odd I hodd, norm_div, norm_pow]
  have hnorm : ‖(normalizedGaussianIdealGenerator I hodd : ℂ)‖ ^ 2 =
      (I.absNorm : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normalizedGaussianIdealGenerator_complex_normSq I hodd
  rw [hnorm]
  simp [hpos.ne']

theorem norm_gaussianNuIdealWeight_le_one
    (I : Ideal (𝓞 GaussianField)) :
    ‖gaussianNuIdealWeight I‖ ≤ 1 := by
  by_cases hodd : (I.absNorm : ZMod 2) = 1
  · rw [norm_gaussianNuIdealWeight_eq_one_of_odd I hodd]
  · rw [gaussianNuIdealWeight_of_even I hodd]
    simp

theorem gaussianNuIdealWeight_top : gaussianNuIdealWeight ⊤ = 1 := by
  have hodd : ((⊤ : Ideal (𝓞 GaussianField)).absNorm : ZMod 2) = 1 := by simp
  have hnorm := norm_gaussianNuIdealWeight_eq_one_of_odd ⊤ hodd
  have hmul : gaussianNuIdealWeight ⊤ =
      gaussianNuIdealWeight ⊤ * gaussianNuIdealWeight ⊤ := by
    simpa using gaussianNuIdealWeight_mul ⊤ ⊤
  have hnonzero : gaussianNuIdealWeight ⊤ ≠ 0 := by
    intro hz
    simp [hz] at hnorm
  have hcancel : gaussianNuIdealWeight ⊤ * 1 =
      gaussianNuIdealWeight ⊤ * gaussianNuIdealWeight ⊤ := by
    simpa using hmul
  exact (mul_left_cancel₀ hnonzero hcancel).symm

/-- The CM twist relevant to the quartic trace constituent. -/
noncomputable def gaussianEtaIdealWeight
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I : Ideal (𝓞 GaussianField)) : ℂ :=
  gaussianNuIdealWeight I * (quarticIdealWeight R ι I)⁻¹

theorem gaussianEtaIdealWeight_mul
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I J : Ideal (𝓞 GaussianField)) :
    gaussianEtaIdealWeight R ι (I * J) =
      gaussianEtaIdealWeight R ι I * gaussianEtaIdealWeight R ι J := by
  simp [gaussianEtaIdealWeight, gaussianNuIdealWeight_mul,
    GaussianIdealLBound.quarticIdealCoeff_weight_mul, mul_inv_rev]
  ring

theorem gaussianEtaIdealWeight_top
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) :
    gaussianEtaIdealWeight R ι ⊤ = 1 := by
  have hgood : GaussianQuarticGoodIdeal R ⊤ := by
    refine ⟨by simp, ?_⟩
    intro P hP
    have hunit : IsUnit P.asIdeal := isUnit_of_dvd_one (by simpa using hP)
    exact (P.isPrime.ne_top (Ideal.isUnit_iff.mp hunit)).elim
  have hnorm : ‖quarticIdealWeight R ι ⊤‖ = 1 := by
    simp only [quarticIdealWeight, dif_pos hgood]
    exact norm_gaussianQuarticComplexValue ι _
  have hmul : quarticIdealWeight R ι ⊤ =
      quarticIdealWeight R ι ⊤ * quarticIdealWeight R ι ⊤ := by
    simpa using GaussianIdealLBound.quarticIdealCoeff_weight_mul R ι ⊤ ⊤
  have hnonzero : quarticIdealWeight R ι ⊤ ≠ 0 := by
    intro hz
    simp [hz] at hnorm
  have hψ : quarticIdealWeight R ι ⊤ = 1 := by
    have hcancel : quarticIdealWeight R ι ⊤ * 1 =
        quarticIdealWeight R ι ⊤ * quarticIdealWeight R ι ⊤ := by
      simpa using hmul
    exact (mul_left_cancel₀ hnonzero hcancel).symm
  simp [gaussianEtaIdealWeight, gaussianNuIdealWeight_top, hψ]

theorem norm_gaussianEtaIdealWeight_le_one
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (I : Ideal (𝓞 GaussianField)) :
    ‖gaussianEtaIdealWeight R ι I‖ ≤ 1 := by
  by_cases hgood : GaussianQuarticGoodIdeal R I
  · have hψ : ‖quarticIdealWeight R ι I‖ = 1 := by
      simp only [quarticIdealWeight, dif_pos hgood]
      exact norm_gaussianQuarticComplexValue ι _
    rw [gaussianEtaIdealWeight, norm_mul, norm_inv, hψ, inv_one, mul_one]
    exact norm_gaussianNuIdealWeight_le_one I
  · simp [gaussianEtaIdealWeight, quarticIdealWeight, hgood]

theorem odd_norm_of_gaussianParityNormalized (z : GaussianInt)
    (hz : GaussianParityNormalized z) :
    (z.norm : ZMod 2) = 1 := by
  rcases hz with ⟨hre, him⟩
  simp [Zsqrtd.norm, sub_eq_add_neg, hre, him]

theorem gaussianPrincipalIdeal_odd_of_normalized (z : GaussianInt)
    (hz : GaussianParityNormalized z) :
    ((gaussianPrincipalIdeal z).absNorm : ZMod 2) = 1 := by
  rw [absNorm_gaussianPrincipalIdeal]
  have hcast := congrArg (fun n : ℤ => (n : ZMod 2))
    (GaussianInt.abs_natCast_norm z)
  simpa [odd_norm_of_gaussianParityNormalized z hz] using hcast

/-- For a normalized generator, the CM character is its squared direction. -/
theorem gaussianNuIdealWeight_of_normalized (z : GaussianInt)
    (hz : GaussianParityNormalized z) :
    gaussianNuIdealWeight (gaussianPrincipalIdeal z) =
      angularTwo (z : ℂ) := by
  have hodd := gaussianPrincipalIdeal_odd_of_normalized z hz
  have hsq := normalizedGaussianIdealGenerator_sq_eq
    (gaussianPrincipalIdeal z) hodd z rfl hz
  have hnorm : Complex.normSq (z : ℂ) =
      ((gaussianPrincipalIdeal z).absNorm : ℝ) := by
    have hcomplex := GaussianInt.intCast_complex_norm z
    have hnormz : z.norm.natAbs = (gaussianPrincipalIdeal z).absNorm := by
      rw [← absNorm_gaussianPrincipalIdeal]
    have hnat : (z.norm : ℝ) =
        ((gaussianPrincipalIdeal z).absNorm : ℝ) := by
      rw [← GaussianInt.abs_natCast_norm z]
      exact_mod_cast hnormz
    have hcomplex' : ((Complex.normSq (z : ℂ) : ℝ) : ℂ) =
        ((gaussianPrincipalIdeal z).absNorm : ℂ) := by
      rw [← hcomplex]
      exact_mod_cast hnat
    exact_mod_cast hcomplex'
  have hznonzero : (z : ℂ) ≠ 0 := by
    intro hzero
    have hnormzero : (z : ℂ) = 0 := hzero
    simp [hnormzero] at hnorm
    have hodd' := hodd
    have habs : (gaussianPrincipalIdeal z).absNorm = 0 := by
      exact_mod_cast hnorm.symm
    simp [habs] at hodd'
  rw [gaussianNuIdealWeight_of_odd _ hodd]
  rw [← map_pow, hsq, map_pow]
  simp only [angularTwo, if_neg hznonzero, div_pow]
  rw [Complex.normSq_eq_norm_sq] at hnorm
  have hnormC := congrArg (fun x : ℝ => (x : ℂ)) hnorm
  have hnormC' : ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ((gaussianPrincipalIdeal z).absNorm : ℂ) := by
    simpa using hnormC
  rw [← hnormC']
  simp

theorem gaussianPrincipalIdeal_norm_parity (z : GaussianInt) :
    ((gaussianPrincipalIdeal z).absNorm : ZMod 2) =
      (z.norm : ZMod 2) := by
  rw [absNorm_gaussianPrincipalIdeal]
  have hcast := congrArg (fun n : ℤ => (n : ZMod 2))
    (GaussianInt.abs_natCast_norm z)
  exact hcast

/-- The CM ideal character is the angular factor corrected by the parity
sign of an arbitrary Gaussian generator. -/
theorem gaussianNuIdealWeight_principal (z : GaussianInt) :
    gaussianNuIdealWeight (gaussianPrincipalIdeal z) =
      gaussianParitySign z * angularTwo (z : ℂ) := by
  by_cases hodd : (z.norm : ZMod 2) = 1
  · rcases gaussian_odd_norm_parity z hodd with hnormalized | ⟨hre, him⟩
    · rw [gaussianNuIdealWeight_of_normalized z hnormalized,
        gaussianParitySign_of_normalized z hnormalized]
      simp
    · let zi : GaussianInt := z * Zsqrtd.sqrtd
      have hnormalized : GaussianParityNormalized zi := by
        constructor
        · simp [zi, Zsqrtd.re_mul, him]
        · simp [zi, Zsqrtd.im_mul, hre]
      have hspan : gaussianPrincipalIdeal zi = gaussianPrincipalIdeal z := by
        exact gaussianPrincipalIdeal_mul_i z
      have hcast : (zi : ℂ) = Complex.I * (z : ℂ) := by
        have hi : ((Zsqrtd.sqrtd : GaussianInt) : ℂ) = Complex.I := by
          simp [GaussianInt.toComplex_def]
        rw [show zi = z * Zsqrtd.sqrtd from rfl,
          GaussianInt.toComplex_mul, hi, mul_comm]
      rw [← hspan, gaussianNuIdealWeight_of_normalized zi hnormalized,
        hcast, angularTwo_quarter_turn,
        gaussianParitySign_of_im_odd z hre him]
      ring
  · have heven : (z.norm : ZMod 2) = 0 :=
      zmod_two_eq_zero_of_ne_one _ hodd
    have hIeven : ((gaussianPrincipalIdeal z).absNorm : ZMod 2) ≠ 1 := by
      rw [gaussianPrincipalIdeal_norm_parity, heven]
      exact zero_ne_one
    rw [gaussianNuIdealWeight_of_even _ hIeven,
      gaussianParitySign_of_even_norm z heven]
    simp

/-- The finite residue weight that accompanies the angular factor in the
Gaussian generator series for `η`. -/
noncomputable def gaussianEtaLatticeWeight
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (p : ℤ × ℤ) : ℂ :=
  gaussianPointParitySign p *
    (quarticIdealLatticeWeight R ι p)⁻¹

theorem gaussianEtaLatticeWeight_angular
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (p : ℤ × ℤ) :
    gaussianEtaLatticeWeight R ι p * angularTwo (integerPairComplex p) =
      gaussianEtaIdealWeight R ι
        (gaussianPrincipalIdeal (⟨p.1, p.2⟩ : GaussianInt)) := by
  let z : GaussianInt := ⟨p.1, p.2⟩
  have hcomplex : integerPairComplex p = (z : ℂ) := by
    simp [integerPairComplex, z, GaussianInt.toComplex_def, mul_comm]
  have hideal : quarticIdealLatticeWeight R ι p =
      quarticIdealWeight R ι (gaussianPrincipalIdeal z) := by
    exact quarticIdealLatticeWeight_eq_idealWeight R ι p
  rw [gaussianEtaLatticeWeight, gaussianEtaIdealWeight,
    gaussianNuIdealWeight_principal z, hcomplex, hideal]
  dsimp [gaussianPointParitySign, z]
  ring

/-- Norm-indexed coefficients of the CM-twisted quartic ideal character. -/
noncomputable def gaussianEtaIdealCoeff
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    ∑ I ∈ gaussianAllIdealNormShell n, gaussianEtaIdealWeight R ι I

theorem gaussianEtaAngularCoeff_eq_four_idealCoeff
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (n : ℕ) :
    gaussianWeightCoeff (gaussianEtaLatticeWeight R ι) n =
      4 * gaussianEtaIdealCoeff R ι n := by
  by_cases hn : n = 0
  · subst n
    have hs : gaussianNormShell 0 = {(0, 0)} := by
      ext p
      rw [mem_gaussianNormShell_iff, gaussianNormSq_eq_zero_iff]
      simp
    simp [gaussianWeightCoeff, hs, gaussianEtaIdealCoeff,
      angularTwo, integerPairComplex]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    unfold gaussianWeightCoeff
    calc
      (∑ p ∈ gaussianNormShell n,
          gaussianEtaLatticeWeight R ι p * angularTwo (integerPairComplex p)) =
          ∑ p ∈ gaussianNormShell n,
            gaussianEtaIdealWeight R ι
              (gaussianPrincipalIdeal (⟨p.1, p.2⟩ : GaussianInt)) := by
            apply Finset.sum_congr rfl
            intro p _
            exact gaussianEtaLatticeWeight_angular R ι p
      _ = ∑ z ∈ gaussianIntegerNormShell n,
            gaussianEtaIdealWeight R ι (gaussianPrincipalIdeal z) := by
            convert gaussianNormShell_sum_eq_integerShell n
              (fun z => gaussianEtaIdealWeight R ι (gaussianPrincipalIdeal z)) using 1
            apply Finset.sum_congr rfl
            intro p _
            rfl
      _ = 4 * ∑ I ∈ gaussianIdealNormShell n,
            gaussianEtaIdealWeight R ι I :=
          gaussian_shell_sum_eq_four_ideal_sum n hpos (gaussianEtaIdealWeight R ι)
      _ = 4 * gaussianEtaIdealCoeff R ι n := by
            rw [gaussianIdealNormShell_eq_all]
            simp [gaussianEtaIdealCoeff, hn]

theorem gaussianEtaAngularLSeries_eq_four_idealLSeries
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ) (s : ℂ) :
    LSeries (gaussianWeightCoeff (gaussianEtaLatticeWeight R ι)) s =
      4 * LSeries (gaussianEtaIdealCoeff R ι) s := by
  have hcoeff : gaussianWeightCoeff (gaussianEtaLatticeWeight R ι) =
      (4 : ℂ) • gaussianEtaIdealCoeff R ι := by
    funext n
    simpa [Pi.smul_apply] using
      gaussianEtaAngularCoeff_eq_four_idealCoeff R ι n
  rw [hcoeff, LSeries_smul]

theorem quarticIdealLatticeWeight_quarter_turn
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (p : ℤ × ℤ) :
    quarticIdealLatticeWeight R ι
      (GaussianZeroMean.gaussianPairMul (0, 1) p) =
        quarticIdealLatticeWeight R ι p := by
  have hturn : GaussianZeroMean.gaussianPairMul (0, 1) p =
      (-p.2, p.1) := by
    simp [GaussianZeroMean.gaussianPairMul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [hturn, quarticIdealLatticeWeight_eq_idealWeight,
    quarticIdealLatticeWeight_eq_idealWeight]
  change quarticIdealWeight R ι
    (gaussianPrincipalIdeal (⟨-p.2, p.1⟩ : GaussianInt)) =
      quarticIdealWeight R ι
        (gaussianPrincipalIdeal (⟨p.1, p.2⟩ : GaussianInt))
  have hi : (⟨-p.2, p.1⟩ : GaussianInt) =
      (⟨p.1, p.2⟩ : GaussianInt) * Zsqrtd.sqrtd := by
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [hi, gaussianPrincipalIdeal_mul_i]

theorem gaussianEtaLatticeWeight_periodic
    (q : ℕ) (hq : Even q)
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (hψperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι)) :
    PeriodicGaussianWeight q (gaussianEtaLatticeWeight R ι) := by
  intro i j u v
  simp only [gaussianEtaLatticeWeight]
  rw [gaussianPointParitySign_periodic q hq i j u v,
    hψperiod i j u v]

theorem gaussianEtaLatticeWeight_residue_mean_zero
    (q : ℕ) [NeZero q] (hq : Even q)
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (hψperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι)) :
    (∑ uv : Fin q × Fin q,
      residueWeight q (gaussianEtaLatticeWeight R ι) uv) = 0 := by
  apply gaussianSignTwist_residue_sum_zero q hq
    (fun p => (quarticIdealLatticeWeight R ι p)⁻¹)
  · intro i j u v
    exact congrArg Inv.inv (hψperiod i j u v)
  · intro p
    rw [quarticIdealLatticeWeight_quarter_turn]

theorem norm_gaussianEtaLatticeWeight_le_one
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (p : ℤ × ℤ) :
    ‖gaussianEtaLatticeWeight R ι p‖ ≤ 1 := by
  by_cases hgood : GaussianQuarticGoodIdeal R
      (Ideal.span {gaussianPointInteger p})
  · have hψ : ‖quarticIdealLatticeWeight R ι p‖ = 1 := by
      simp only [quarticIdealLatticeWeight, dif_pos hgood]
      exact norm_gaussianQuarticComplexValue ι _
    rw [gaussianEtaLatticeWeight, norm_mul, norm_inv, hψ, inv_one, mul_one]
    exact norm_gaussianParitySign_le_one _
  · have hψ : quarticIdealLatticeWeight R ι p = 0 := by
      simp [quarticIdealLatticeWeight, hgood]
    simp [gaussianEtaLatticeWeight, hψ]

theorem norm_gaussianEtaIdealLSeries_le_log
    (q : ℕ) [NeZero q] (hq : Even q)
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (hψperiod : PeriodicGaussianWeight q (quarticIdealLatticeWeight R ι))
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianEtaIdealCoeff R ι) (σ : ℂ)‖ ≤
      (162 * Real.log ((q : ℝ) ^ 2) + 648) / 4 := by
  have hperiod := gaussianEtaLatticeWeight_periodic q hq R ι hψperiod
  have hmean := gaussianEtaLatticeWeight_residue_mean_zero q hq R ι hψperiod
  have h := norm_gaussianWeightLSeries_le_log q (gaussianEtaLatticeWeight R ι)
    hperiod hmean
    (fun uv => norm_gaussianEtaLatticeWeight_le_one R ι _) σ hσ₁ hσ₂
  rw [gaussianEtaAngularLSeries_eq_four_idealLSeries, norm_mul] at h
  have hfour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  rw [hfour] at h
  linarith

/-- For any nonzero rational radicand the concrete quartic conductor
`64 |R|` supplies all finite-period hypotheses automatically. No
nonprincipality assumption is needed for infinity type two: the parity sign
itself makes the residue mean zero. -/
theorem norm_gaussianEtaIdealLSeries_le_log_signed
    (R : ℤ) (hR0 : R ≠ 0)
    (ι : GaussianField →+* ℂ)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianEtaIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖ ≤
      (162 * Real.log (((64 * R.natAbs : ℕ) : ℝ) ^ 2) + 648) / 4 := by
  letI : NeZero (64 * R.natAbs) := ⟨by omega⟩
  have heven : Even (64 * R.natAbs) := by
    refine ⟨32 * R.natAbs, ?_⟩
    omega
  exact norm_gaussianEtaIdealLSeries_le_log (64 * R.natAbs) heven
    (R : 𝓞 GaussianField) ι
    (quarticIdealLatticeWeight_any_signed_periodic R hR0 ι)
    σ hσ₁ hσ₂

/-- Compatibility alias for the odd-radicand case. -/
theorem norm_gaussianEtaIdealLSeries_le_log_signed_odd
    (R : ℤ) (hR0 : R ≠ 0) (_hRodd : Odd R)
    (ι : GaussianField →+* ℂ)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (gaussianEtaIdealCoeff (R : 𝓞 GaussianField) ι) (σ : ℂ)‖ ≤
      (162 * Real.log (((64 * R.natAbs : ℕ) : ℝ) ^ 2) + 648) / 4 :=
  norm_gaussianEtaIdealLSeries_le_log_signed R hR0 ι σ hσ₁ hσ₂

end Erdos940.Quartic.GaussianCMCharacter
