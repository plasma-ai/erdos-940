import Erdos940.Quartic.GaussianCMParity
import Erdos940.Quartic.GaussianHeckeLBridge
import Erdos940.Quartic.GaussianZeroMean

/-!
# The mod-two sign of a Gaussian integer

The sign is `1` on odd-real/even-imaginary Gaussian integers, `-1` on the
opposite parity class, and zero when the norm is even. Its change under a
quarter-turn cancels the change of an infinity-type-two angular weight.
-/

namespace Erdos940.Quartic

/-- The mod-two indicator of an odd integer, viewed in `ℂ`. -/
def gaussianParityBit (n : ℤ) : ℂ :=
  if (n : ZMod 2) = 1 then 1 else 0

/-- The coordinate-parity sign used to select an odd Gaussian generator. -/
def gaussianParitySign (z : GaussianInt) : ℂ :=
  gaussianParityBit z.re - gaussianParityBit z.im

/-- The same sign on integer lattice points. -/
def gaussianPointParitySign (p : ℤ × ℤ) : ℂ :=
  gaussianParitySign (⟨p.1, p.2⟩ : GaussianInt)

theorem gaussianParitySign_of_normalized (z : GaussianInt)
    (hz : GaussianParityNormalized z) : gaussianParitySign z = 1 := by
  simp [gaussianParitySign, gaussianParityBit, hz.1, hz.2]

theorem gaussianParitySign_of_im_odd (z : GaussianInt)
    (hre : (z.re : ZMod 2) = 0)
    (him : (z.im : ZMod 2) = 1) : gaussianParitySign z = -1 := by
  simp [gaussianParitySign, gaussianParityBit, hre, him]

/-- The sign vanishes precisely on the parity classes with even norm. -/
theorem gaussianParitySign_of_even_norm (z : GaussianInt)
    (hz : (z.norm : ZMod 2) = 0) : gaussianParitySign z = 0 := by
  have hnorm : (z.re : ZMod 2) * (z.re : ZMod 2) +
      (z.im : ZMod 2) * (z.im : ZMod 2) = 0 := by
    simpa [Zsqrtd.norm, sub_eq_add_neg] using hz
  have hbinary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hbinary (z.re : ZMod 2) with hre | hre <;>
    rcases hbinary (z.im : ZMod 2) with him | him
  all_goals simp [gaussianParitySign, gaussianParityBit, hre, him] at *

theorem gaussianParityBit_neg (n : ℤ) :
    gaussianParityBit (-n) = gaussianParityBit n := by
  simp [gaussianParityBit, ZMod.neg_eq_self_mod_two]

/-- A quarter-turn exchanges the odd-real and odd-imaginary classes. -/
theorem gaussianParitySign_mul_i (z : GaussianInt) :
    gaussianParitySign (z * Zsqrtd.sqrtd) = -gaussianParitySign z := by
  simp [gaussianParitySign, gaussianParityBit_neg, Zsqrtd.re_mul,
    Zsqrtd.im_mul]

/-- Negating a generator does not change its parity sign. -/
theorem gaussianParitySign_neg (z : GaussianInt) :
    gaussianParitySign (-z) = gaussianParitySign z := by
  simp [gaussianParitySign, gaussianParityBit_neg]

/-- The sign takes only the values `-1`, `0`, and `1`. -/
theorem gaussianParitySign_eq_cases (z : GaussianInt) :
    gaussianParitySign z = -1 ∨ gaussianParitySign z = 0 ∨
      gaussianParitySign z = 1 := by
  unfold gaussianParitySign gaussianParityBit
  split_ifs <;> norm_num

theorem norm_gaussianParitySign_le_one (z : GaussianInt) :
    ‖gaussianParitySign z‖ ≤ 1 := by
  rcases gaussianParitySign_eq_cases z with h | h | h <;> simp [h]

theorem gaussianPointParitySign_periodic (q : ℕ) (hq : Even q) :
    GaussianHeckeLBridge.PeriodicGaussianWeight q gaussianPointParitySign := by
  intro i j u v
  have hq0 : (q : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr hq
  simp [gaussianPointParitySign, gaussianParitySign, gaussianParityBit,
    GaussianCellPartition.signedCellPoint, hq0]

/-- Multiplication by `i` reverses the sign on integer lattice points. -/
theorem gaussianPointParitySign_pairMul_i (p : ℤ × ℤ) :
    gaussianPointParitySign (GaussianZeroMean.gaussianPairMul (0, 1) p) =
      -gaussianPointParitySign p := by
  have hi : (⟨p.1, p.2⟩ : GaussianInt) * Zsqrtd.sqrtd =
      (⟨-p.2, p.1⟩ : GaussianInt) := by
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
  have h := gaussianParitySign_mul_i (⟨p.1, p.2⟩ : GaussianInt)
  rw [hi] at h
  simpa [gaussianPointParitySign, GaussianZeroMean.gaussianPairMul,
    Zsqrtd.re_mul, Zsqrtd.im_mul] using h

/-- A quarter-turn invariant periodic weight becomes mean-zero after
twisting by the Gaussian parity sign. -/
theorem gaussianSignTwist_residue_sum_zero
    (q : ℕ) [NeZero q] (hq : Even q)
    (ψ : ℤ × ℤ → ℂ)
    (hψperiod : GaussianHeckeLBridge.PeriodicGaussianWeight q ψ)
    (hψturn : ∀ p, ψ (GaussianZeroMean.gaussianPairMul (0, 1) p) = ψ p) :
    (∑ uv : Fin q × Fin q,
      GaussianHeckeLBridge.residueWeight q
        (fun p => gaussianPointParitySign p * ψ p) uv) = 0 := by
  let w : ℤ × ℤ → ℂ := fun p => gaussianPointParitySign p * ψ p
  have hwperiod : GaussianHeckeLBridge.PeriodicGaussianWeight q w := by
    intro i j u v
    dsimp [w]
    rw [gaussianPointParitySign_periodic q hq i j u v, hψperiod i j u v]
  have ht : (1 : ZMod q) *
      (((0 : ℤ) : ZMod q) ^ 2 + ((1 : ℤ) : ZMod q) ^ 2) = 1 := by simp
  let e := GaussianZeroMean.gaussianFinResidueMulEquiv q (0, 1) 1 ht
  apply GaussianHeckeLBridge.residue_sum_zero_of_eigenvalue q
    (GaussianHeckeLBridge.residueWeight q w) e (-1) (by norm_num)
  intro uv
  rw [show e uv = GaussianCellPartition.cellOffset q (NeZero.pos q)
      (GaussianZeroMean.gaussianPairMul (0, 1)
        (GaussianCellPartition.signedCellPoint q 0 0 uv.1 uv.2)) from
      GaussianZeroMean.gaussianFinResidueMulEquiv_apply q (0, 1) 1 ht uv]
  rw [← GaussianHeckeLBridge.periodic_weight_eq_residueWeight q (NeZero.pos q)
    w hwperiod]
  dsimp [w, GaussianHeckeLBridge.residueWeight]
  rw [gaussianPointParitySign_pairMul_i, hψturn]
  ring

end Erdos940.Quartic
