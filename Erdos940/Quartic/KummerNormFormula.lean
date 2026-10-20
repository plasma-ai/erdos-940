import ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

/-!
# The binary quadratic norm of a degree-two Kummer algebra
-/

namespace Erdos940.Quartic

open Polynomial Module

private noncomputable abbrev quadPoly (K : Type*) [Field K] (a : Kˣ) : K[X] :=
  X ^ ((2 : ℕ+) : ℕ) - C (a : K)

private abbrev quadAlg (K : Type*) [Field K] (a : Kˣ) :=
  ClassFieldTheory.KummerAlgebra K (2 : ℕ+) a

private noncomputable def quadBasis (K : Type*) [Field K] (a : Kˣ) :
    Basis (Fin 2) K (quadAlg K a) := by
  let p := quadPoly K a
  have hm : p.Monic := Polynomial.monic_X_pow_sub_C (a : K)
    (by norm_num : ((2 : ℕ+) : ℕ) ≠ 0)
  have hd : p.natDegree = 2 := by simp [p, quadPoly]
  exact (AdjoinRoot.powerBasisAux' hm).reindex (finCongr hd)

theorem kummer_norm_binary_formula (K : Type*) [Field K] (a : Kˣ) (x y : K) :
    Algebra.norm K (algebraMap K (quadAlg K a) x +
      algebraMap K (quadAlg K a) y * AdjoinRoot.root (quadPoly K a)) =
      x ^ 2 - (a : K) * y ^ 2 := by
  classical
  let B := quadBasis K a
  have hB (i : Fin 2) : B i = AdjoinRoot.root (quadPoly K a) ^ (i : ℕ) := by
    simp only [B, quadBasis, Basis.reindex_apply]
    exact (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C (a : K)
      (by norm_num : ((2 : ℕ+) : ℕ) ≠ 0))).basis_eq_pow _
  have hroot : AdjoinRoot.root (quadPoly K a) ^ 2 =
      algebraMap K (quadAlg K a) (a : K) := by
    have h : Polynomial.aeval (AdjoinRoot.root (quadPoly K a))
        (quadPoly K a) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    dsimp only [quadPoly] at h
    rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] at h
    exact sub_eq_zero.mp h
  have hr0 : AdjoinRoot.root (quadPoly K a) = B 1 := by
    simpa using (hB 1).symm
  have hr1 : AdjoinRoot.root (quadPoly K a) ^ 2 = (a : K) • B 0 := by
    simpa [hB, Algebra.smul_def] using hroot
  have hcol0 (i : Fin 2) :
      Algebra.leftMulMatrix B (AdjoinRoot.root (quadPoly K a)) i 0 =
        if i = 1 then 1 else 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hb0 : B 0 = 1 := by simpa using hB 0
    rw [hb0, mul_one, hr0, Basis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  have hcol1 (i : Fin 2) :
      Algebra.leftMulMatrix B (AdjoinRoot.root (quadPoly K a)) i 1 =
        if i = 0 then (a : K) else 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    rw [← hr0, ← pow_two, hr1, map_smul, Basis.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  have hMat : Algebra.leftMulMatrix B (AdjoinRoot.root (quadPoly K a)) =
      !![0, (a : K); 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hcol0, hcol1]
  rw [Algebra.norm_eq_matrix_det B]
  rw [map_add, map_mul, (Algebra.leftMulMatrix B).commutes x,
    (Algebra.leftMulMatrix B).commutes y, hMat]
  simp [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.algebraMap_eq_diagonal]
  ring

/-- A degree-two Kummer norm is exactly the corresponding binary quadratic form. -/
theorem isKummerNorm_two_iff_binary_form (K : Type*) [Field K] (a b : Kˣ) :
    ClassFieldTheory.IsKummerNorm K (2 : ℕ+) a b ↔
      ∃ x y : K, x ^ 2 - (a : K) * y ^ 2 = (b : K) := by
  classical
  constructor
  · rintro ⟨z, hz⟩
    let B := quadBasis K a
    let x := B.repr (z : quadAlg K a) 0
    let y := B.repr (z : quadAlg K a) 1
    have hB (i : Fin 2) : B i = AdjoinRoot.root (quadPoly K a) ^ (i : ℕ) := by
      simp only [B, quadBasis, Basis.reindex_apply]
      exact (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C (a : K)
        (by norm_num : ((2 : ℕ+) : ℕ) ≠ 0))).basis_eq_pow _
    have hb0 : B 0 = 1 := by simpa using hB 0
    have hb1 : B 1 = AdjoinRoot.root (quadPoly K a) := by simpa using hB 1
    have hcoord : (z : quadAlg K a) =
        algebraMap K (quadAlg K a) x +
          algebraMap K (quadAlg K a) y * AdjoinRoot.root (quadPoly K a) := by
      have h := (B.sum_repr (z : quadAlg K a)).symm
      rw [Fin.sum_univ_two] at h
      simpa [x, y, hb0, hb1, Algebra.smul_def] using h
    refine ⟨x, y, ?_⟩
    rw [← kummer_norm_binary_formula K a x y, ← hcoord]
    exact hz
  · rintro ⟨x, y, hxy⟩
    let z : quadAlg K a := algebraMap K (quadAlg K a) x +
      algebraMap K (quadAlg K a) y * AdjoinRoot.root (quadPoly K a)
    let z' : quadAlg K a := algebraMap K (quadAlg K a) x -
      algebraMap K (quadAlg K a) y * AdjoinRoot.root (quadPoly K a)
    have hroot : AdjoinRoot.root (quadPoly K a) ^ 2 =
        algebraMap K (quadAlg K a) (a : K) := by
      have h : Polynomial.aeval (AdjoinRoot.root (quadPoly K a))
          (quadPoly K a) = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      dsimp only [quadPoly] at h
      rw [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C] at h
      exact sub_eq_zero.mp h
    have hprod : z * z' = algebraMap K (quadAlg K a) (b : K) := by
      calc
        z * z' = (algebraMap K (quadAlg K a) x) ^ 2 -
            (algebraMap K (quadAlg K a) y) ^ 2 *
              AdjoinRoot.root (quadPoly K a) ^ 2 := by dsimp [z, z']; ring
        _ = algebraMap K (quadAlg K a) (x ^ 2 - (a : K) * y ^ 2) := by
          rw [hroot]; simp only [map_sub, map_pow, map_mul]; ring
        _ = algebraMap K (quadAlg K a) (b : K) := by rw [hxy]
    have hzUnit : IsUnit z := by
      apply isUnit_of_dvd_unit ⟨z', hprod.symm⟩
      exact (Units.isUnit b).map (algebraMap K (quadAlg K a))
    obtain ⟨u, hu⟩ := hzUnit
    refine ⟨u, ?_⟩
    rw [hu]
    exact (kummer_norm_binary_formula K a x y).trans hxy

end Erdos940.Quartic
