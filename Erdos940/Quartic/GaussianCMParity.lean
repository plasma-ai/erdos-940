import Erdos940.Quartic.JacobiGaussianGenerator

/-!
# Parity normalization in the Gaussian integers

An odd-norm Gaussian integer has one odd coordinate and one even coordinate.
Multiplication by a Gaussian unit puts the odd coordinate in the real part.
The normalized elements are closed under multiplication, and two normalized
generators of the same principal ideal differ only by sign.
-/

namespace Erdos940.Quartic

/-- The coordinatewise mod-two normalization used for CM generators. -/
def GaussianParityNormalized (z : GaussianInt) : Prop :=
  (z.re : ZMod 2) = 1 ∧ (z.im : ZMod 2) = 0

/-- An odd Gaussian norm forces exactly one coordinate to be odd. -/
theorem gaussian_odd_norm_parity (z : GaussianInt)
    (hz : (z.norm : ZMod 2) = 1) :
    GaussianParityNormalized z ∨
      ((z.re : ZMod 2) = 0 ∧ (z.im : ZMod 2) = 1) := by
  have hnorm : (z.re : ZMod 2) * (z.re : ZMod 2) +
      (z.im : ZMod 2) * (z.im : ZMod 2) = 1 := by
    simpa [Zsqrtd.norm, sub_eq_add_neg] using hz
  have hbinary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hre := hbinary (z.re : ZMod 2)
  have him := hbinary (z.im : ZMod 2)
  rcases hre with hre | hre <;> rcases him with him | him
  · simp [hre, him] at hnorm
  · exact Or.inr ⟨hre, him⟩
  · exact Or.inl ⟨hre, him⟩
  · simp [hre, him] at hnorm

/-- Every odd-norm Gaussian integer can be normalized by `1` or `i`. -/
theorem gaussian_odd_norm_normalize (z : GaussianInt)
    (hz : (z.norm : ZMod 2) = 1) :
    ∃ u : GaussianInt, IsUnit u ∧ GaussianParityNormalized (z * u) := by
  rcases gaussian_odd_norm_parity z hz with h | ⟨hre, him⟩
  · exact ⟨1, isUnit_one, by simpa [GaussianParityNormalized] using h⟩
  · refine ⟨Zsqrtd.sqrtd, ?_, ?_⟩
    · apply (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) _).mp
      norm_num [Zsqrtd.norm]
    · constructor
      · simp [Zsqrtd.re_mul, him]
      · simp [Zsqrtd.im_mul, hre]

/-- The odd-real, even-imaginary normalization is multiplicatively closed. -/
theorem gaussianParityNormalized_mul (z w : GaussianInt)
    (hz : GaussianParityNormalized z)
    (hw : GaussianParityNormalized w) :
    GaussianParityNormalized (z * w) := by
  rcases hz with ⟨hzre, hzim⟩
  rcases hw with ⟨hwre, hwim⟩
  constructor
  · simp [Zsqrtd.re_mul, hzre, hzim, hwre, hwim]
  · simp [Zsqrtd.im_mul, hzre, hzim, hwre, hwim]

/-- Two parity-normalized associated Gaussian integers differ by a sign. -/
theorem gaussianParityNormalized_associated_eq_sign
    (z w u : GaussianInt) (hu : IsUnit u) (hw : w = z * u)
    (hz : GaussianParityNormalized z)
    (hwn : GaussianParityNormalized w) :
    w = z ∨ w = -z :=
  gaussian_associated_eq_sign_of_parity z w u hu hw hz.1 hz.2 hwn.2

/-- Squaring removes the remaining sign ambiguity of normalized generators. -/
theorem gaussianParityNormalized_associated_square_eq
    (z w u : GaussianInt) (hu : IsUnit u) (hw : w = z * u)
    (hz : GaussianParityNormalized z)
    (hwn : GaussianParityNormalized w) :
    w ^ 2 = z ^ 2 := by
  rcases gaussianParityNormalized_associated_eq_sign z w u hu hw hz hwn with h | h
  · rw [h]
  · rw [h, neg_sq]

end Erdos940.Quartic
