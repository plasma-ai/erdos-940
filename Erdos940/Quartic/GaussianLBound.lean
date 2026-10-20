import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Finite cancellation in the Gaussian lattice estimate

The elementary estimate for a Gaussian Hecke L-series begins with a lattice
Riemann sum over residue classes.  The two cancellation mechanisms for its
common integral are finite: a nontrivial finite character has zero mean, and
an infinity-type-two character has zero mean by a quarter turn.  The results
below isolate these facts and the norm estimate that transfers a uniform
per-class discrepancy to a weighted lattice sum.  They make no assertion
about the geometric discrepancy itself.
-/

namespace Erdos940.Quartic.GaussianLBound

open Finset

/-- A nontrivial character of a finite multiplicative group has mean zero. -/
theorem sum_nontrivial_character_eq_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : χ ≠ 1) : (∑ g : G, χ g) = 0 := by
  classical
  have h : ∃ g : G, χ g ≠ 1 := by
    by_contra hn
    apply hχ
    ext g
    exact not_not.mp (not_exists.mp hn g)
  obtain ⟨g, hg⟩ := h
  let S : ℂ := ∑ x : G, χ x
  have htrans : χ g * S = S := by
    calc
      χ g * S = ∑ x : G, χ (g * x) := by simp [S, map_mul, Finset.mul_sum]
      _ = S := by
        simpa [S] using (Equiv.sum_comp (Equiv.mulLeft g) (fun x : G => χ x))
  have hzero : (χ g - 1) * S = 0 := by
    calc
      (χ g - 1) * S = χ g * S - S := by ring
      _ = 0 := sub_eq_zero.mpr htrans
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hg)

/-- A finite residue character cancels over the whole quotient ring as soon
as it is nontrivial on one invertible residue.  Values at nonunits may be
zero, as they are for imprimitive Hecke characters. -/
theorem sum_residue_character_eq_zero {M : Type*} [Monoid M] [Fintype M]
    (ω : M →* ℂ) (u : Mˣ) (hu : ω (u : M) ≠ 1) :
    (∑ a : M, ω a) = 0 := by
  classical
  let S : ℂ := ∑ a : M, ω a
  have htrans : ω (u : M) * S = S := by
    calc
      ω (u : M) * S = ∑ a : M, ω ((u : M) * a) := by
        simp [S, map_mul, Finset.mul_sum]
      _ = S := by
        simpa [S] using (Equiv.sum_comp (Units.mulLeft u) (fun a : M => ω a))
  have hzero : (ω (u : M) - 1) * S = 0 := by
    calc
      (ω (u : M) - 1) * S = ω (u : M) * S - S := by ring
      _ = 0 := sub_eq_zero.mpr htrans
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hu)

/-- The finite cancellation used for infinity type two.  It only needs a
quarter-turn permutation on residue classes and anti-invariance of the
weight, so it also applies to imprimitive characters. -/
theorem sum_quarter_turn_antiinvariant_eq_zero {A : Type*} [Fintype A]
    (turn : A ≃ A) (ω : A → ℂ)
    (hω : ∀ a, ω (turn a) = -ω a) : (∑ a : A, ω a) = 0 := by
  classical
  have hturn : (∑ a : A, ω a) = ∑ a : A, ω (turn a) := by
    exact (Equiv.sum_comp turn ω).symm
  have hneg : (∑ a : A, ω a) = -∑ a : A, ω a := by
    calc
      (∑ a : A, ω a) = ∑ a : A, ω (turn a) := hturn
      _ = ∑ a : A, -ω a := Finset.sum_congr rfl (fun a _ => hω a)
      _ = -∑ a : A, ω a := by simp
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hneg)

/-- Rotation by `i` on the square residue lattice.  This is the concrete
permutation behind the type-two cancellation when the Gaussian modulus is
enlarged to a rational integer. -/
def gaussianQuarterTurn (q : ℕ) : (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun a := (-a.2, a.1)
  invFun a := (a.2, -a.1)
  left_inv := by intro a; simp
  right_inv := by intro a; simp

/-- The type-two finite weight has zero mean over a rational Gaussian
modulus.  Anti-invariance is exactly the compatibility of the finite part of
the Hecke character with the unit `i`. -/
theorem gaussian_residue_type_two_mean_zero (q : ℕ) [NeZero q]
    (ω : ZMod q × ZMod q → ℂ)
    (hω : ∀ a, ω (-a.2, a.1) = -ω a) :
    (∑ a : ZMod q × ZMod q, ω a) = 0 :=
  sum_quarter_turn_antiinvariant_eq_zero (gaussianQuarterTurn q) ω hω

/-- A complete `q × q` block of residues has zero character sum, even
after translating the block.  This is the exact cancellation used for the
interior cells of a disk tiling. -/
theorem gaussian_complete_residue_block_zero (q : ℕ) [NeZero q]
    (ω : ZMod q × ZMod q → ℂ)
    (hω : (∑ r : ZMod q × ZMod q, ω r) = 0)
    (a : ZMod q × ZMod q) :
    (∑ p : Fin q × Fin q,
      ω (a + ((ZMod.finEquiv q p.1), (ZMod.finEquiv q p.2)))) = 0 := by
  classical
  let e : (Fin q × Fin q) ≃ (ZMod q × ZMod q) :=
    (ZMod.finEquiv q).toEquiv.prodCongr (ZMod.finEquiv q).toEquiv
  calc
    (∑ p : Fin q × Fin q,
        ω (a + ((ZMod.finEquiv q p.1), (ZMod.finEquiv q p.2)))) =
        ∑ r : ZMod q × ZMod q, ω (a + r) := by
          simpa [e, Prod.map] using
            (Equiv.sum_comp e (fun r : ZMod q × ZMod q => ω (a + r)))
    _ = ∑ r : ZMod q × ZMod q, ω r :=
      Equiv.sum_comp (Equiv.addLeft a) ω
    _ = 0 := hω

/-- The angular factor of an infinity-type-two Gaussian Hecke character,
extended by zero at the origin. -/
noncomputable def angularTwo (z : ℂ) : ℂ :=
  if z = 0 then 0 else (z / (‖z‖ : ℂ)) ^ 2

/-- A quarter turn reverses the type-two angular factor. -/
theorem angularTwo_quarter_turn (z : ℂ) :
    angularTwo (Complex.I * z) = -angularTwo z := by
  by_cases hz : z = 0
  · simp [angularTwo, hz]
  have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hn : ‖Complex.I * z‖ = ‖z‖ := by simp
  simp only [angularTwo, ite_eq_right hz, ite_eq_right hIz, hn]
  rw [mul_div_assoc, mul_pow]
  simp

/-- The angular factor is unitary away from zero. -/
theorem norm_angularTwo_le_one (z : ℂ) : ‖angularTwo z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [angularTwo, hz]
  simp [angularTwo, hz, norm_pow, Complex.norm_real]

/-- Quantitative variation of the normalized direction in a real normed
space.  This is the elementary angular-gradient estimate in discrete form. -/
theorem norm_normalize_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (z w : V) (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖NormedSpace.normalize z - NormedSpace.normalize w‖ ≤
      2 * ‖z - w‖ / ‖z‖ := by
  let u := NormedSpace.normalize z
  let v := NormedSpace.normalize w
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hv : ‖v‖ = 1 := NormedSpace.norm_normalize hw
  have hid : ‖z‖ • (u - v) = (z - w) + (‖w‖ - ‖z‖) • v := by
    dsimp [u, v]
    simp only [smul_sub, sub_smul, NormedSpace.norm_smul_normalize]
    abel
  have hrev : |‖w‖ - ‖z‖| ≤ ‖z - w‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le w z
  have hle : ‖z‖ * ‖u - v‖ ≤ 2 * ‖z - w‖ := by
    calc
      ‖z‖ * ‖u - v‖ = ‖‖z‖ • (u - v)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hzpos]
      _ = ‖(z - w) + (‖w‖ - ‖z‖) • v‖ := by rw [hid]
      _ ≤ ‖z - w‖ + ‖(‖w‖ - ‖z‖) • v‖ := norm_add_le _ _
      _ = ‖z - w‖ + |‖w‖ - ‖z‖| := by simp [norm_smul, hv, Real.norm_eq_abs]
      _ ≤ 2 * ‖z - w‖ := by linarith
  exact (le_div_iff₀ hzpos).2 (by simpa [u, v, mul_comm] using hle)

theorem angularTwo_eq_normalize_sq (z : ℂ) :
    angularTwo z = (NormedSpace.normalize z) ^ 2 := by
  by_cases hz : z = 0
  · simp [angularTwo, hz]
  simp [angularTwo, hz, NormedSpace.normalize, div_eq_mul_inv]
  ring

/-- Discrete angular-gradient bound for infinity type two.  The denominator
uses the first point only; swapping the arguments gives the corresponding
bound with the second point. -/
theorem norm_angularTwo_sub_le (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖angularTwo z - angularTwo w‖ ≤ 4 * ‖z - w‖ / ‖z‖ := by
  let u := NormedSpace.normalize z
  let v := NormedSpace.normalize w
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hz
  have hv : ‖v‖ = 1 := NormedSpace.norm_normalize hw
  have huv : ‖u + v‖ ≤ 2 := by
    calc
      ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ = 2 := by rw [hu, hv]; norm_num
  have hdiff : ‖u - v‖ ≤ 2 * ‖z - w‖ / ‖z‖ :=
    norm_normalize_sub_le z w hz hw
  calc
    ‖angularTwo z - angularTwo w‖ = ‖(u - v) * (u + v)‖ := by
      rw [angularTwo_eq_normalize_sq, angularTwo_eq_normalize_sq]
      dsimp [u, v]
      congr 1
      ring
    _ = ‖u - v‖ * ‖u + v‖ := norm_mul _ _
    _ ≤ (2 * ‖z - w‖ / ‖z‖) * 2 :=
      mul_le_mul hdiff huv (norm_nonneg _) (by positivity)
    _ = 4 * ‖z - w‖ / ‖z‖ := by ring

theorem norm_angularTwo_sub_le_any (z w : ℂ) (hz : z ≠ 0) :
    ‖angularTwo z - angularTwo w‖ ≤ 4 * ‖z - w‖ / ‖z‖ := by
  by_cases hw : w = 0
  · subst w
    simp [angularTwo, hz]
  · exact norm_angularTwo_sub_le z w hz hw

/-- Complex lattice point in cell `(i,j)` with offsets `(u,v)` and side
length `q`. -/
def cellPoint (q i j u v : ℕ) : ℂ :=
  ((i * q + u : ℕ) : ℂ) + ((j * q + v : ℕ) : ℂ) * Complex.I

theorem norm_cellBase_ge_max (q i j : ℕ) :
    (q : ℝ) * (max i j : ℝ) ≤ ‖cellPoint q i j 0 0‖ := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right (by exact_mod_cast hij : (i : ℝ) ≤ j)]
    have h := Complex.im_le_norm (cellPoint q i j 0 0)
    simpa [cellPoint, mul_comm] using h
  · rw [max_eq_left (by exact_mod_cast hji : (j : ℝ) ≤ i)]
    have h := Complex.re_le_norm (cellPoint q i j 0 0)
    simpa [cellPoint, mul_comm] using h

theorem norm_cellPoint_sub_base_le (q i j u v : ℕ)
    (hu : u < q) (hv : v < q) :
    ‖cellPoint q i j u v - cellPoint q i j 0 0‖ ≤ 2 * (q : ℝ) := by
  have hdiff : cellPoint q i j u v - cellPoint q i j 0 0 =
      (u : ℂ) + (v : ℂ) * Complex.I := by
    simp [cellPoint]
    ring
  rw [hdiff]
  calc
    ‖(u : ℂ) + (v : ℂ) * Complex.I‖ ≤
        ‖(u : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = (u : ℝ) + v := by simp
    _ ≤ 2 * (q : ℝ) := by exact_mod_cast (by omega : u + v ≤ 2 * q)

theorem cellPoint_ne_zero_of_max_pos (q i j u v : ℕ)
    (hq : 0 < q) (hk : 0 < max i j) : cellPoint q i j u v ≠ 0 := by
  by_cases hi : 0 < i
  · have hcoord : 0 < i * q + u := by
      have := Nat.mul_pos hi hq
      omega
    intro hz
    have hzre := congrArg Complex.re hz
    simp [cellPoint] at hzre
    have : (0 : ℝ) < i * q + u := by exact_mod_cast hcoord
    linarith
  · have hj : 0 < j := by
      have hi0 : i = 0 := by omega
      simpa [hi0] using hk
    have hcoord : 0 < j * q + v := by
      have := Nat.mul_pos hj hq
      omega
    intro hz
    have hzim := congrArg Complex.im hz
    simp [cellPoint] at hzim
    have : (0 : ℝ) < j * q + v := by exact_mod_cast hcoord
    linarith

/-- Variation of the angular weight inside a noncentral square cell.  The
point is assumed nonzero; this follows automatically in the first quadrant
when `max i j > 0`, and the explicit premise also accommodates translated
cells in other quadrants. -/
theorem norm_angularTwo_cell_sub_base_le (q i j u v : ℕ)
    (hq : 0 < q) (hk : 0 < max i j) (hu : u < q) (hv : v < q) :
    ‖angularTwo (cellPoint q i j 0 0) -
      angularTwo (cellPoint q i j u v)‖ ≤ 8 / (max i j : ℝ) := by
  let z := cellPoint q i j 0 0
  let w := cellPoint q i j u v
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hkpos : (0 : ℝ) < max (i : ℝ) (j : ℝ) := by
    simpa only [Nat.cast_max] using (show (0 : ℝ) < (max i j : ℝ) by exact_mod_cast hk)
  have hbase : (q : ℝ) * (max i j : ℝ) ≤ ‖z‖ := norm_cellBase_ge_max q i j
  have hzpos : 0 < ‖z‖ := (mul_pos hqpos hkpos).trans_le hbase
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have hdist : ‖z - w‖ ≤ 2 * (q : ℝ) := by
    simpa only [norm_sub_rev, z, w] using norm_cellPoint_sub_base_le q i j u v hu hv
  have ha := norm_angularTwo_sub_le z w hz
    (cellPoint_ne_zero_of_max_pos q i j u v hq hk)
  have ha' : ‖angularTwo z - angularTwo w‖ * ‖z‖ ≤ 4 * ‖z - w‖ :=
    (le_div_iff₀ hzpos).mp ha
  have hnonneg : 0 ≤ ‖angularTwo z - angularTwo w‖ := norm_nonneg _
  have hcomp := mul_le_mul_of_nonneg_left hbase hnonneg
  have hqmul : (q : ℝ) *
      (‖angularTwo z - angularTwo w‖ * max (i : ℝ) (j : ℝ)) ≤ (q : ℝ) * 8 := by
    nlinarith
  have hresult : ‖angularTwo z - angularTwo w‖ * max (i : ℝ) (j : ℝ) ≤ 8 :=
    le_of_mul_le_mul_left hqmul hqpos
  simpa only [Nat.cast_max] using (le_div_iff₀ hkpos).2 hresult

/-- Integer lattice points in the box of radius `R`. -/
def integerBox (R : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(R : ℤ)) R).product (Finset.Icc (-(R : ℤ)) R)

/-- A finite disk, expressed as lattice points in a containing box. -/
def integerDisk (R : ℕ) : Finset (ℤ × ℤ) :=
  (integerBox R).filter fun p => p.1 ^ 2 + p.2 ^ 2 ≤ (R : ℤ) ^ 2

/-- The box gives a direct linear-in-area upper bound on disk points. -/
theorem integerDisk_card_le_box (R : ℕ) :
    (integerDisk R).card ≤ (integerBox R).card :=
  Finset.card_filter_le _ _

theorem integerBox_card (R : ℕ) :
    (integerBox R).card = (2 * R + 1) ^ 2 := by
  have hI : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
    have hZ := Int.card_Icc_of_le (a := -(R : ℤ)) (b := R) (by omega)
    have hZ' : ((Finset.Icc (-(R : ℤ)) R).card : ℤ) = (2 * R + 1 : ℕ) := by
      convert hZ using 1
      push_cast
      ring
    exact_mod_cast hZ'
  simp [integerBox, Finset.card_product, hI, pow_two]

/-- The number of integer lattice points in a disk is bounded by the
surrounding square.  This is the elementary absolute-count input for the
head of a Gaussian ideal Dirichlet series. -/
theorem integerDisk_card_le (R : ℕ) :
    (integerDisk R).card ≤ (2 * R + 1) ^ 2 := by
  rw [← integerBox_card]
  exact integerDisk_card_le_box R

/-- A Gaussian integer of squared norm at most `X` lies in the square of
radius `⌊√X⌋`. -/
theorem mem_integerBox_of_normSq_le (X : ℕ) (p : ℤ × ℤ)
    (hp : p.1 ^ 2 + p.2 ^ 2 ≤ (X : ℤ)) :
    p ∈ integerBox (Nat.sqrt X) := by
  have hp1 : p.1 ^ 2 ≤ (X : ℤ) := by nlinarith [sq_nonneg p.2]
  have hp2 : p.2 ^ 2 ≤ (X : ℤ) := by nlinarith [sq_nonneg p.1]
  have hsq1 : ((p.1.natAbs ^ 2 : ℕ) : ℤ) = p.1 ^ 2 := by simp
  have hsq2 : ((p.2.natAbs ^ 2 : ℕ) : ℤ) = p.2 ^ 2 := by simp
  have h1nat : p.1.natAbs ^ 2 ≤ X := by exact_mod_cast (hsq1 ▸ hp1)
  have h2nat : p.2.natAbs ^ 2 ≤ X := by exact_mod_cast (hsq2 ▸ hp2)
  have h1 : p.1.natAbs ≤ Nat.sqrt X := Nat.le_sqrt'.mpr h1nat
  have h2 : p.2.natAbs ≤ Nat.sqrt X := Nat.le_sqrt'.mpr h2nat
  change p ∈ (Finset.Icc (-(Nat.sqrt X : ℤ)) (Nat.sqrt X)).product
    (Finset.Icc (-(Nat.sqrt X : ℤ)) (Nat.sqrt X))
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- All integer pairs of squared norm at most `X`, as a finite set. -/
def integerNormBall (X : ℕ) : Finset (ℤ × ℤ) :=
  (integerBox (Nat.sqrt X)).filter fun p => p.1 ^ 2 + p.2 ^ 2 ≤ (X : ℤ)

theorem mem_integerNormBall_iff (X : ℕ) (p : ℤ × ℤ) :
    p ∈ integerNormBall X ↔ p.1 ^ 2 + p.2 ^ 2 ≤ (X : ℤ) := by
  simp only [integerNormBall, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨mem_integerBox_of_normSq_le X p h, h⟩⟩

/-- Coarse area bound for Gaussian integer norms. -/
theorem integerNormBall_card_le_nine_mul (X : ℕ) (hX : 0 < X) :
    (integerNormBall X).card ≤ 9 * X := by
  have hcard : (integerNormBall X).card ≤ (2 * Nat.sqrt X + 1) ^ 2 := by
    calc
      (integerNormBall X).card ≤ (integerBox (Nat.sqrt X)).card :=
        Finset.card_filter_le _ _
      _ = (2 * Nat.sqrt X + 1) ^ 2 := integerBox_card _
  have hsqrt : (Nat.sqrt X) ^ 2 ≤ X := Nat.sqrt_le' X
  have hsqrt_le : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
  have hsq : (2 * Nat.sqrt X + 1) ^ 2 ≤ 9 * X := by nlinarith
  exact hcard.trans hsq

/-- Quarter turn on the actual integer lattice. -/
def integerQuarterTurn : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (-p.2, p.1)
  invFun p := (p.2, -p.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

theorem integerQuarterTurn_preserves_normBall (X : ℕ) (p : ℤ × ℤ) :
    integerQuarterTurn p ∈ integerNormBall X ↔ p ∈ integerNormBall X := by
  simp [mem_integerNormBall_iff, integerQuarterTurn, add_comm]

/-- The complex point represented by an integer lattice pair. -/
def integerPairComplex (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

theorem integerPairComplex_quarter_turn (p : ℤ × ℤ) :
    integerPairComplex (integerQuarterTurn p) =
      Complex.I * integerPairComplex p := by
  simp [integerPairComplex, integerQuarterTurn]
  calc
    -(p.2 : ℂ) + (p.1 : ℂ) * Complex.I =
        Complex.I * (p.1 : ℂ) + (p.2 : ℂ) * (Complex.I * Complex.I) := by
          rw [Complex.I_mul_I]
          ring
    _ = Complex.I * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by ring

/-- The type-two angular factor cancels exactly over every centered
integer disk.  This is a finite counterpart of the vanishing common angular
integral in the lattice Riemann-sum argument. -/
theorem angularTwo_integerNormBall_sum_zero (X : ℕ) :
    ∑ p ∈ integerNormBall X, angularTwo (integerPairComplex p) = 0 := by
  classical
  let S := integerNormBall X
  let turnS : {p : ℤ × ℤ // p ∈ S} ≃ {p : ℤ × ℤ // p ∈ S} := {
    toFun := fun p => ⟨integerQuarterTurn p.1,
      (integerQuarterTurn_preserves_normBall X p.1).mpr p.2⟩
    invFun := fun p => ⟨integerQuarterTurn.symm p.1, by
      have h : integerQuarterTurn (integerQuarterTurn.symm p.1) ∈ S := by simp [p.2]
      exact (integerQuarterTurn_preserves_normBall X _).mp h⟩
    left_inv := by intro p; apply Subtype.ext; simp [integerQuarterTurn]
    right_inv := by intro p; apply Subtype.ext; simp [integerQuarterTurn]
  }
  have hsum := sum_quarter_turn_antiinvariant_eq_zero turnS
    (fun p : {p : ℤ × ℤ // p ∈ S} => angularTwo (integerPairComplex p.1)) (by
      intro p
      exact (integerPairComplex_quarter_turn p.1).symm ▸
        angularTwo_quarter_turn (integerPairComplex p.1))
  change (∑ p ∈ S, angularTwo (integerPairComplex p)) = 0
  rw [← Finset.sum_attach]
  exact hsum

/-- Cancellation of the common main term in a weighted lattice Riemann
sum.  With `A` the classes modulo a Gaussian modulus, `F a` is the disk sum
in class `a`, `I` is its common integral, and `E` is the cell error in (6).
The character values have norm at most one. -/
theorem norm_weighted_sum_le_card_mul_error {A : Type*} [Fintype A]
    (ω F : A → ℂ) (I : ℂ) (E : ℝ) (hω : (∑ a : A, ω a) = 0)
    (hunit : ∀ a, ‖ω a‖ ≤ 1) (herr : ∀ a, ‖F a - I‖ ≤ E) :
    ‖∑ a : A, ω a * F a‖ ≤ Fintype.card A * E := by
  classical
  have hmain : (∑ a : A, ω a * I) = 0 := by
    rw [← Finset.sum_mul, hω, zero_mul]
  have hrewrite : (∑ a : A, ω a * (F a - I)) = ∑ a : A, ω a * F a := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hmain, sub_zero]
  calc
    ‖∑ a : A, ω a * F a‖ = ‖∑ a : A, ω a * (F a - I)‖ := by rw [hrewrite]
    _ ≤ ∑ a : A, ‖ω a * (F a - I)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : A, E := by
      apply Finset.sum_le_sum
      intro a _
      calc
        ‖ω a * (F a - I)‖ = ‖ω a‖ * ‖F a - I‖ := norm_mul _ _
        _ ≤ 1 * E := mul_le_mul (hunit a) (herr a) (norm_nonneg _) zero_le_one
        _ = E := one_mul _
    _ = Fintype.card A * E := by simp

/-- The exact finite-to-geometric reduction for a rational Gaussian modulus
`q`.  A disk-cell estimate with error `E` in each of the `q²` classes gives
this total estimate. -/
theorem gaussian_residue_weighted_sum_le (q : ℕ) [NeZero q]
    (ω F : ZMod q × ZMod q → ℂ) (I : ℂ) (E : ℝ)
    (hω : ∀ a, ω (-a.2, a.1) = -ω a)
    (hunit : ∀ a, ‖ω a‖ ≤ 1) (herr : ∀ a, ‖F a - I‖ ≤ E) :
    ‖∑ a : ZMod q × ZMod q, ω a * F a‖ ≤ (q : ℝ) ^ 2 * E := by
  have h := norm_weighted_sum_le_card_mul_error ω F I E
    (gaussian_residue_type_two_mean_zero q ω hω) hunit herr
  simpa [Fintype.card_prod, ZMod.card, pow_two] using h

/-- Algebraic form of (7) for a rational Gaussian modulus: a per-class
error of `r / q + 1` yields `q r + q²`.  In the disk application `r = √X`
and `Q = q²`. -/
theorem gaussian_residue_bound_from_cell_error (q : ℕ) [NeZero q]
    (ω F : ZMod q × ZMod q → ℂ) (I : ℂ) (r : ℝ)
    (hω : ∀ a, ω (-a.2, a.1) = -ω a)
    (hunit : ∀ a, ‖ω a‖ ≤ 1)
    (herr : ∀ a, ‖F a - I‖ ≤ r / (q : ℝ) + 1) :
    ‖∑ a : ZMod q × ZMod q, ω a * F a‖ ≤ (q : ℝ) * r + (q : ℝ) ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  calc
    ‖∑ a : ZMod q × ZMod q, ω a * F a‖ ≤
        (q : ℝ) ^ 2 * (r / (q : ℝ) + 1) :=
      gaussian_residue_weighted_sum_le q ω F I _ hω hunit herr
    _ = (q : ℝ) * r + (q : ℝ) ^ 2 := by field_simp

/-- A complete noncentral Gaussian cell has small weighted angular sum.
The finite weight has mean zero over one period, and the angular factor
varies by at most `8/max(i,j)` across the cell. -/
theorem norm_complete_cell_sum_le (q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ p : Fin q × Fin q, ω p) = 0)
    (hunit : ∀ p, ‖ω p‖ ≤ 1) (i j : ℕ) (hk : 0 < max i j) :
    ‖∑ p : Fin q × Fin q,
      ω p * angularTwo (cellPoint q i j p.1 p.2)‖ ≤
      (q : ℝ) ^ 2 * (8 / (max i j : ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  have herr (p : Fin q × Fin q) :
      ‖angularTwo (cellPoint q i j p.1 p.2) -
        angularTwo (cellPoint q i j 0 0)‖ ≤ 8 / (max i j : ℝ) := by
    simpa only [norm_sub_rev] using
      norm_angularTwo_cell_sub_base_le q i j p.1 p.2 hq hk p.1.isLt p.2.isLt
  have h := norm_weighted_sum_le_card_mul_error ω
    (fun p : Fin q × Fin q => angularTwo (cellPoint q i j p.1 p.2))
    (angularTwo (cellPoint q i j 0 0)) (8 / (max i j : ℝ)) hmean hunit herr
  simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using h

/-! ### Signed cells for the global disk partition -/

/-- A cell based at a signed Gaussian lattice coordinate. -/
def signedCellPoint (q : ℕ) (i j : ℤ) (u v : ℕ) : ℂ :=
  ((i * (q : ℤ) + u : ℤ) : ℂ) +
    ((j * (q : ℤ) + v : ℤ) : ℂ) * Complex.I

theorem norm_signedCellBase_ge_max (q : ℕ) (i j : ℤ) :
    (q : ℝ) * (max i.natAbs j.natAbs : ℝ) ≤
      ‖signedCellPoint q i j 0 0‖ := by
  rcases le_total i.natAbs j.natAbs with hij | hji
  · rw [max_eq_right (show (i.natAbs : ℝ) ≤ j.natAbs by exact_mod_cast hij)]
    have h := Complex.abs_im_le_norm (signedCellPoint q i j 0 0)
    simpa [signedCellPoint, abs_mul, Nat.cast_natAbs, mul_comm] using h
  · rw [max_eq_left (show (j.natAbs : ℝ) ≤ i.natAbs by exact_mod_cast hji)]
    have h := Complex.abs_re_le_norm (signedCellPoint q i j 0 0)
    simpa [signedCellPoint, abs_mul, Nat.cast_natAbs, mul_comm] using h

theorem norm_signedCellPoint_sub_base_le (q : ℕ) (i j : ℤ) (u v : ℕ)
    (hu : u < q) (hv : v < q) :
    ‖signedCellPoint q i j u v - signedCellPoint q i j 0 0‖ ≤
      2 * (q : ℝ) := by
  have hdiff : signedCellPoint q i j u v - signedCellPoint q i j 0 0 =
      (u : ℂ) + (v : ℂ) * Complex.I := by
    simp [signedCellPoint]
    ring
  rw [hdiff]
  calc
    ‖(u : ℂ) + (v : ℂ) * Complex.I‖ ≤
        ‖(u : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = (u : ℝ) + v := by simp
    _ ≤ 2 * (q : ℝ) := by exact_mod_cast (by omega : u + v ≤ 2 * q)

/-- Angular variation in a signed square cell, measured from its lattice
corner. The estimate remains valid if the cell contains the origin. -/
theorem norm_angularTwo_signedCell_sub_base_le (q : ℕ) (i j : ℤ)
    (u v : ℕ) (hq : 0 < q) (hk : 0 < max i.natAbs j.natAbs)
    (hu : u < q) (hv : v < q) :
    ‖angularTwo (signedCellPoint q i j 0 0) -
      angularTwo (signedCellPoint q i j u v)‖ ≤
      8 / (max i.natAbs j.natAbs : ℝ) := by
  let z := signedCellPoint q i j 0 0
  let w := signedCellPoint q i j u v
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hkpos : (0 : ℝ) < (max i.natAbs j.natAbs : ℝ) := by exact_mod_cast hk
  have hbase : (q : ℝ) * (max i.natAbs j.natAbs : ℝ) ≤ ‖z‖ :=
    norm_signedCellBase_ge_max q i j
  have hzpos : 0 < ‖z‖ := (mul_pos hqpos hkpos).trans_le hbase
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have hdist : ‖z - w‖ ≤ 2 * (q : ℝ) := by
    simpa only [norm_sub_rev, z, w] using
      norm_signedCellPoint_sub_base_le q i j u v hu hv
  have ha := norm_angularTwo_sub_le_any z w hz
  have ha' : ‖angularTwo z - angularTwo w‖ * ‖z‖ ≤ 4 * ‖z - w‖ :=
    (le_div_iff₀ hzpos).mp ha
  have hnonneg : 0 ≤ ‖angularTwo z - angularTwo w‖ := norm_nonneg _
  have hcomp := mul_le_mul_of_nonneg_left hbase hnonneg
  have hqmul : (q : ℝ) *
      (‖angularTwo z - angularTwo w‖ * (max i.natAbs j.natAbs : ℝ)) ≤
      (q : ℝ) * 8 := by nlinarith
  have hresult : ‖angularTwo z - angularTwo w‖ *
      (max i.natAbs j.natAbs : ℝ) ≤ 8 :=
    le_of_mul_le_mul_left hqmul hqpos
  exact (le_div_iff₀ hkpos).2 hresult

/-- A signed noncentral cell has a uniformly bounded weighted angular sum
when the coefficient pattern has zero mean over a full period. -/
theorem norm_complete_signedCell_sum_le (q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ)
    (hmean : (∑ p : Fin q × Fin q, ω p) = 0)
    (hunit : ∀ p, ‖ω p‖ ≤ 1) (i j : ℤ)
    (hk : 0 < max i.natAbs j.natAbs) :
    ‖∑ p : Fin q × Fin q,
      ω p * angularTwo (signedCellPoint q i j p.1 p.2)‖ ≤
      (q : ℝ) ^ 2 * (8 / (max i.natAbs j.natAbs : ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  have herr (p : Fin q × Fin q) :
      ‖angularTwo (signedCellPoint q i j p.1 p.2) -
        angularTwo (signedCellPoint q i j 0 0)‖ ≤
        8 / (max i.natAbs j.natAbs : ℝ) := by
    simpa only [norm_sub_rev] using
      norm_angularTwo_signedCell_sub_base_le q i j p.1 p.2 hq hk p.1.isLt p.2.isLt
  have h := norm_weighted_sum_le_card_mul_error ω
    (fun p : Fin q × Fin q => angularTwo (signedCellPoint q i j p.1 p.2))
    (angularTwo (signedCellPoint q i j 0 0))
    (8 / (max i.natAbs j.natAbs : ℝ)) hmean hunit herr
  simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using h

/-- A partial cell costs at most its number of lattice points. This is used
for cells intersecting the disk boundary and for the central cell. -/
theorem norm_partial_signedCell_sum_le (q : ℕ) [NeZero q]
    (ω : Fin q × Fin q → ℂ) (hunit : ∀ p, ‖ω p‖ ≤ 1)
    (i j : ℤ) (T : Finset (Fin q × Fin q)) :
    ‖∑ p ∈ T, ω p * angularTwo (signedCellPoint q i j p.1 p.2)‖ ≤
      (q : ℝ) ^ 2 := by
  have hterm (p : Fin q × Fin q) :
      ‖ω p * angularTwo (signedCellPoint q i j p.1 p.2)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      ‖ω p‖ * ‖angularTwo (signedCellPoint q i j p.1 p.2)‖ ≤ 1 * 1 :=
        mul_le_mul (hunit p) (norm_angularTwo_le_one _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  calc
    ‖∑ p ∈ T, ω p * angularTwo (signedCellPoint q i j p.1 p.2)‖ ≤
        ∑ p ∈ T, ‖ω p * angularTwo (signedCellPoint q i j p.1 p.2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      exact hterm p
    _ = (T.card : ℝ) := by simp
    _ ≤ (q : ℝ) ^ 2 := by
      have hcard : T.card ≤ q ^ 2 := by
        calc
          T.card ≤ Fintype.card (Fin q × Fin q) := Finset.card_le_univ _
          _ = q ^ 2 := by simp [Fintype.card_prod, pow_two]
      exact_mod_cast hcard

end Erdos940.Quartic.GaussianLBound
