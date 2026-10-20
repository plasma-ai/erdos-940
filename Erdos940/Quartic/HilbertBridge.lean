import Erdos940.Quartic.Hilbert
import Erdos940.Quartic.KummerNormFormula

/-!
# Finite obstructions from Hilbert reciprocity

The quartic proof needs a finite-place obstruction for a positive definite
quaternary quadratic form of square determinant. Hilbert reciprocity gives a
finite Kummer nonnorm; the quadratic norm formula and Pfister normalization
turn it into anisotropy of the original form at a finite completion.
-/

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

/-- The image of a global scalar in a finite completion. -/
noncomputable def finitePlaceScalar
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : F) : v.adicCompletion F :=
  algebraMap F (v.adicCompletion F) x

/-- The image of a global unit in a finite completion. -/
noncomputable def finitePlaceUnit
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a

theorem finitePlaceUnit_val
    (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    (finitePlaceUnit F v a : v.adicCompletion F) =
      finitePlaceScalar F v (a : F) := rfl

theorem finitePlaceScalar_ratCast
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) :
    finitePlaceScalar ℚ v x = (x : v.adicCompletion ℚ) := by
  simp [finitePlaceScalar]

theorem finitePlaceUnit_ratCast
    (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℚˣ) :
    (finitePlaceUnit ℚ v a : v.adicCompletion ℚ) =
      ((a : ℚ) : v.adicCompletion ℚ) := by
  rw [finitePlaceUnit_val, finitePlaceScalar_ratCast]

/-- A nontrivial product of infinite Hilbert factors forces a nontrivial
finite local factor in a coherent Hilbert-pairing family. -/
theorem exists_finite_hilbert_obstruction
    (F : Type*) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (a b : Fˣ)
    (hInfinite : (∏ v : InfinitePlace F,
      ClassFieldTheory.globalInfinitePlaceHilbertSymbol F n v a b) ≠ 1) :
    ∃ B : ClassFieldTheory.GlobalHilbertPairingFamily F n,
      ClassFieldTheory.GlobalHilbertPairingFamily.IsLocallyHilbert F B ∧
      ∃ v : HeightOneSpectrum (𝓞 F),
        ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor
          F B hmu v a b ≠ 1 := by
  classical
  obtain ⟨B, hLocal, _hSupport, hProduct⟩ :=
    ClassFieldTheory.exists_globalHilbertPairingFamily_productFormula F n hmu
  refine ⟨B, hLocal, ?_⟩
  by_contra hnone
  have hall (v : HeightOneSpectrum (𝓞 F)) :
      ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor
        F B hmu v a b = 1 := by
    by_contra hv
    exact hnone ⟨v, hv⟩
  have hfinite :
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor
          F B hmu v a b) = 1 :=
    finprod_eq_one_of_forall_eq_one hall
  have h := hProduct a b
  rw [hfinite, mul_one] at h
  exact hInfinite h

/-- A local Kummer norm has trivial finite Hilbert factor. -/
theorem finite_hilbert_factor_eq_one_of_kummer_norm
    (F : Type*) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : ClassFieldTheory.GlobalHilbertPairingFamily F n)
    (hLocal : ClassFieldTheory.GlobalHilbertPairingFamily.IsLocallyHilbert F B)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ)
    (hnorm : ClassFieldTheory.IsKummerNorm (v.adicCompletion F) n
      (finitePlaceUnit F v a) (finitePlaceUnit F v b)) :
    ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor F B hmu v a b = 1 := by
  have hs : (B v).symbol
      (finitePlaceUnit F v a) (finitePlaceUnit F v b) = 1 :=
    (ClassFieldTheory.localHilbertPairing_eq_one_iff_isKummerNorm
      (v.adicCompletion F) n (B v) (hLocal v) _ _).2 hnorm
  unfold ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor
  dsimp only
  simp only [ClassFieldTheory.HilbertPairing.symbol] at hs
  unfold finitePlaceUnit at hs
  rw [hs]
  exact map_one _

/-- Two negative rational units have a nontrivial factor at the unique real
place for the quadratic Hilbert symbol. -/
theorem rational_negative_infinite_hilbert_factor
    (a b : ℚˣ) (ha : (a : ℚ) < 0) (hb : (b : ℚ) < 0) :
    (∏ v : InfinitePlace ℚ,
      ClassFieldTheory.globalInfinitePlaceHilbertSymbol
        ℚ (2 : ℕ+) v a b) ≠ 1 := by
  classical
  rw [Fintype.prod_unique,
    show (default : InfinitePlace ℚ) = Rat.infinitePlace by
      exact Subsingleton.elim _ _]
  have h : (-1 : ℚˣ) ≠ 1 := by norm_num
  simp [ClassFieldTheory.globalInfinitePlaceHilbertSymbol,
    Rat.isReal_infinitePlace, eq_ratCast, ha, hb]
  intro heq
  exact h (congrArg Subtype.val heq)

/-- The finite obstruction for two negative rational units. -/
theorem exists_rational_finite_hilbert_obstruction
    (a b : ℚˣ) (ha : (a : ℚ) < 0) (hb : (b : ℚ) < 0)
    (hmu : (primitiveRoots 2 ℚ).Nonempty) :
    ∃ B : ClassFieldTheory.GlobalHilbertPairingFamily ℚ (2 : ℕ+),
      ClassFieldTheory.GlobalHilbertPairingFamily.IsLocallyHilbert ℚ B ∧
      ∃ v : HeightOneSpectrum (𝓞 ℚ),
        ClassFieldTheory.GlobalHilbertPairingFamily.finiteFactor
          ℚ B hmu v a b ≠ 1 :=
  exists_finite_hilbert_obstruction ℚ (2 : ℕ+) hmu a b
    (rational_negative_infinite_hilbert_factor a b ha hb)

/-- The finite obstruction can be stated as a failure of the local Kummer norm
criterion, independently of the choice of coherent Hilbert pairing family. -/
theorem exists_rational_finite_kummer_nonnorm
    (a b : ℚˣ) (ha : (a : ℚ) < 0) (hb : (b : ℚ) < 0) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ),
      ¬ ClassFieldTheory.IsKummerNorm (v.adicCompletion ℚ) (2 : ℕ+)
        (finitePlaceUnit ℚ v a) (finitePlaceUnit ℚ v b) := by
  classical
  have hmu : (primitiveRoots 2 ℚ).Nonempty := by
    refine ⟨-1, (mem_primitiveRoots (by decide)).2 ?_⟩
    exact IsPrimitiveRoot.neg_one 0 (by decide)
  obtain ⟨B, hLocal, v, hv⟩ :=
    exists_rational_finite_hilbert_obstruction a b ha hb hmu
  refine ⟨v, ?_⟩
  intro hnorm
  exact hv (finite_hilbert_factor_eq_one_of_kummer_norm
    ℚ (2 : ℕ+) hmu B hLocal v a b hnorm)

/-- The finite nonnorm obstruction in the sign convention of a positive
two-fold Pfister form. -/
theorem exists_positive_pfister_finite_nonnorm
    (u v : ℚˣ) (hu : 0 < (u : ℚ)) (hv : 0 < (v : ℚ)) :
    ∃ w : HeightOneSpectrum (𝓞 ℚ),
      ¬ ClassFieldTheory.IsKummerNorm (w.adicCompletion ℚ) (2 : ℕ+)
        (finitePlaceUnit ℚ w (-u)) (finitePlaceUnit ℚ w (-v)) := by
  apply exists_rational_finite_kummer_nonnorm (-u) (-v)
  · simpa using (neg_lt_zero.mpr hu)
  · simpa using (neg_lt_zero.mpr hv)

/-- A diagonal quaternary form with square coefficient product is a scaled
two-fold Pfister form after rescaling its fourth coordinate. -/
theorem square_determinant_diagonal_normalization
    (K : Type*) [Field K]
    (a b c d t : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ht : t ^ 2 = a * b * c * d) (x y z w : K) :
    a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 =
      a * (x ^ 2 + (b / a) * y ^ 2 + (c / a) * z ^ 2 +
        ((b / a) * (c / a)) * ((t / (b * c)) * w) ^ 2) := by
  field_simp
  linear_combination -w ^ 2 * ht

/-- A nonzero zero of a square-determinant diagonal form gives a nonzero zero
of its normalized two-fold Pfister form. -/
theorem square_determinant_diagonal_isotropic_forward
    (K : Type*) [Field K]
    (a b c d t : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (ht : t ^ 2 = a * b * c * d) (x y z w : K)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)
    (hzero : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 + d * w ^ 2 = 0) :
    ∃ X Y Z W : K,
      (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0 ∨ W ≠ 0) ∧
      X ^ 2 + (b / a) * Y ^ 2 + (c / a) * Z ^ 2 +
        ((b / a) * (c / a)) * W ^ 2 = 0 := by
  have ht0 : t ≠ 0 := by
    intro h
    have hprod : a * b * c * d ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd
    exact hprod (by simpa [h] using ht.symm)
  have hscale : t / (b * c) ≠ 0 := div_ne_zero ht0 (mul_ne_zero hb hc)
  refine ⟨x, y, z, (t / (b * c)) * w, ?_, ?_⟩
  · rcases hnonzero with hx | hy | hz | hw
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr (mul_ne_zero hscale hw)))
  · have hnorm := square_determinant_diagonal_normalization
      K a b c d t ha hb hc ht x y z w
    rw [hnorm] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left ha

/-- Once the binary norm form has a nonzero zero, it represents every scalar. -/
theorem binary_norm_surjective_of_isotropic
    (K : Type*) [Field K] [CharZero K]
    (u x y c : K) (hu : u ≠ 0)
    (hxy : x ≠ 0 ∨ y ≠ 0) (hzero : x ^ 2 + u * y ^ 2 = 0) :
    ∃ p q : K, p ^ 2 + u * q ^ 2 = c := by
  have hy : y ≠ 0 := by
    intro hy0
    have hx0 : x * x = 0 := by simpa [hy0, pow_two] using hzero
    rcases mul_eq_zero.mp hx0 with hx | hx
    · exact hxy.elim (fun h => h hx) (fun h => h hy0)
    · exact hxy.elim (fun h => h hx) (fun h => h hy0)
  obtain ⟨r, hr⟩ : ∃ r : K, r ^ 2 = -u := by
    refine ⟨x / y, ?_⟩
    field_simp
    linear_combination hzero
  have hr0 : r ≠ 0 := by
    intro hr0
    apply hu
    have : -u = 0 := by simpa [hr0] using hr.symm
    exact neg_eq_zero.mp this
  refine ⟨(c + 1) / 2, (1 - c) / (2 * r), ?_⟩
  have htwo : (2 : K) ≠ 0 := by norm_num
  field_simp [hr0, htwo]
  linear_combination (1 - c) ^ 2 * hr

/-- Isotropy of the two-fold Pfister form makes its second negative
coefficient a value of the first binary norm form. -/
theorem pfister_isotropic_implies_binary_norm
    (K : Type*) [Field K] [CharZero K]
    (u v x y z w : K) (hu : u ≠ 0)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)
    (hzero : x ^ 2 + u * y ^ 2 + v * z ^ 2 + u * v * w ^ 2 = 0) :
    ∃ p q : K, p ^ 2 + u * q ^ 2 = -v := by
  obtain ⟨r, hrdef⟩ : ∃ r : K, r = z ^ 2 + u * w ^ 2 := ⟨_, rfl⟩
  have hzero' : x ^ 2 + u * y ^ 2 + v * r = 0 := by
    rw [hrdef]
    linear_combination hzero
  by_cases hr : r = 0
  · have hfirst : x ^ 2 + u * y ^ 2 = 0 := by simpa [hr] using hzero'
    have hsecond : z ^ 2 + u * w ^ 2 = 0 := by rw [← hrdef]; exact hr
    rcases hnonzero with hx | hy | hz | hw
    · exact binary_norm_surjective_of_isotropic K u x y (-v) hu (Or.inl hx) hfirst
    · exact binary_norm_surjective_of_isotropic K u x y (-v) hu (Or.inr hy) hfirst
    · exact binary_norm_surjective_of_isotropic K u z w (-v) hu (Or.inl hz) hsecond
    · exact binary_norm_surjective_of_isotropic K u z w (-v) hu (Or.inr hw) hsecond
  · refine ⟨(x * z + u * y * w) / r, (y * z - x * w) / r, ?_⟩
    have hid : (x * z + u * y * w) ^ 2 + u * (y * z - x * w) ^ 2 =
        (x ^ 2 + u * y ^ 2) * r := by
      rw [hrdef]
      ring
    field_simp [hr]
    linear_combination hid + r * hzero'

/-- The local norm criterion turns a failed Kummer norm into anisotropy of
the corresponding two-fold Pfister form. -/
theorem pfister_anisotropic_of_kummer_nonnorm
    (K : Type*) [Field K] [CharZero K]
    (a b : Kˣ)
    (hNonnorm : ¬ ClassFieldTheory.IsKummerNorm K (2 : ℕ+) a b)
    (x y z w : K)
    (hzero : x ^ 2 - (a : K) * y ^ 2 - (b : K) * z ^ 2 +
      (a : K) * (b : K) * w ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  by_contra htuple
  have hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact htuple hall
  have ha : -(a : K) ≠ 0 := neg_ne_zero.mpr a.ne_zero
  have hpfister : x ^ 2 + (-(a : K)) * y ^ 2 + (-(b : K)) * z ^ 2 +
      (-(a : K)) * (-(b : K)) * w ^ 2 = 0 := by
    convert hzero using 1; ring
  obtain ⟨p, q, hpq⟩ :=
    pfister_isotropic_implies_binary_norm K (-(a : K)) (-(b : K))
      x y z w ha hnonzero hpfister
  apply hNonnorm
  exact (isKummerNorm_two_iff_binary_form K a b).2
    ⟨p, q, by simpa [sub_eq_add_neg] using hpq⟩

/-- A positive rational two-fold Pfister form is anisotropic at some finite
completion. -/
theorem exists_positive_pfister_finite_anisotropic
    (u v : ℚˣ) (hu : 0 < (u : ℚ)) (hv : 0 < (v : ℚ)) :
    ∃ place : HeightOneSpectrum (𝓞 ℚ),
      ∀ x y z w : place.adicCompletion ℚ,
        x ^ 2 + (((u : ℚ) : place.adicCompletion ℚ)) * y ^ 2 +
          (((v : ℚ) : place.adicCompletion ℚ)) * z ^ 2 +
          (((u : ℚ) : place.adicCompletion ℚ)) *
            (((v : ℚ) : place.adicCompletion ℚ)) * w ^ 2 = 0 →
          x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  obtain ⟨place, hNonnorm⟩ := exists_positive_pfister_finite_nonnorm u v hu hv
  refine ⟨place, ?_⟩
  intro x y z w hzero
  let a := finitePlaceUnit ℚ place (-u)
  let b := finitePlaceUnit ℚ place (-v)
  have ha : (a : place.adicCompletion ℚ) =
      -(((u : ℚ) : place.adicCompletion ℚ)) := by
    dsimp [a]
    rw [finitePlaceUnit_ratCast]
    simp
  have hb : (b : place.adicCompletion ℚ) =
      -(((v : ℚ) : place.adicCompletion ℚ)) := by
    dsimp [b]
    rw [finitePlaceUnit_ratCast]
    simp
  have hpfister : x ^ 2 - (a : place.adicCompletion ℚ) * y ^ 2 -
      (b : place.adicCompletion ℚ) * z ^ 2 +
      (a : place.adicCompletion ℚ) * (b : place.adicCompletion ℚ) * w ^ 2 = 0 := by
    rw [ha, hb]
    convert hzero using 1; ring
  exact pfister_anisotropic_of_kummer_nonnorm
    (place.adicCompletion ℚ) a b hNonnorm x y z w hpfister

/-- A positive diagonal quaternary quadratic form whose coefficient product
is a rational square is anisotropic at some finite place. -/
theorem exists_finite_anisotropic_positive_square_det_diagonal
    (a b c d t : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (ht : t ^ 2 = a * b * c * d) :
    ∃ place : HeightOneSpectrum (𝓞 ℚ),
      ∀ x y z w : place.adicCompletion ℚ,
        (((a : place.adicCompletion ℚ) * x ^ 2 +
          (b : place.adicCompletion ℚ) * y ^ 2 +
          (c : place.adicCompletion ℚ) * z ^ 2 +
          (d : place.adicCompletion ℚ) * w ^ 2) = 0) →
          x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hd0 : d ≠ 0 := ne_of_gt hd
  let u : ℚˣ := Units.mk0 (b / a) (div_ne_zero hb0 ha0)
  let v : ℚˣ := Units.mk0 (c / a) (div_ne_zero hc0 ha0)
  have hu : 0 < (u : ℚ) := div_pos hb ha
  have hv : 0 < (v : ℚ) := div_pos hc ha
  obtain ⟨place, hPfister⟩ := exists_positive_pfister_finite_anisotropic u v hu hv
  refine ⟨place, ?_⟩
  have haK : (a : place.adicCompletion ℚ) ≠ 0 := by exact_mod_cast ha0
  have hbK : (b : place.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hb0
  have hcK : (c : place.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hc0
  have hdK : (d : place.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hd0
  have htK : (t : place.adicCompletion ℚ) ^ 2 =
      (a : place.adicCompletion ℚ) * (b : place.adicCompletion ℚ) *
        (c : place.adicCompletion ℚ) * (d : place.adicCompletion ℚ) := by
    exact_mod_cast ht
  have huK : ((u : ℚ) : place.adicCompletion ℚ) =
      (b : place.adicCompletion ℚ) / (a : place.adicCompletion ℚ) := by
    change ((b / a : ℚ) : place.adicCompletion ℚ) = _
    norm_cast
  have hvK : ((v : ℚ) : place.adicCompletion ℚ) =
      (c : place.adicCompletion ℚ) / (a : place.adicCompletion ℚ) := by
    change ((c / a : ℚ) : place.adicCompletion ℚ) = _
    norm_cast
  intro x y z w hzero
  by_contra htuple
  have hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact htuple hall
  obtain ⟨X, Y, Z, W, hNZ, hQ⟩ :=
    square_determinant_diagonal_isotropic_forward
      (place.adicCompletion ℚ) (a : place.adicCompletion ℚ)
      (b : place.adicCompletion ℚ) (c : place.adicCompletion ℚ)
      (d : place.adicCompletion ℚ) (t : place.adicCompletion ℚ)
      haK hbK hcK hdK htK x y z w hnonzero hzero
  have hQ' : X ^ 2 + ((u : ℚ) : place.adicCompletion ℚ) * Y ^ 2 +
      ((v : ℚ) : place.adicCompletion ℚ) * Z ^ 2 +
      ((u : ℚ) : place.adicCompletion ℚ) *
        ((v : ℚ) : place.adicCompletion ℚ) * W ^ 2 = 0 := by
    rw [huK, hvK]
    exact hQ
  obtain ⟨hX, hY, hZ, hW⟩ := hPfister X Y Z W hQ'
  simp [hX, hY, hZ, hW] at hNZ

end Erdos940.Quartic
