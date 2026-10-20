import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-! A local fourth-root lemma in complete ultrametric fields. -/

namespace Erdos940.Quartic

open NNReal

private theorem norm_nat_le_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (n : ℕ) : ‖(n : K)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one K n

private theorem norm_add_bound {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  IsUltrametricDist.norm_add_le_max x y

private theorem norm_core_le_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z : K} (hz : ‖z‖ ≤ 1) : ‖(6 : K) + 4 * z + z ^ 2‖ ≤ 1 := by
  have h6 : ‖(6 : K)‖ ≤ 1 := norm_nat_le_one 6
  have h4 : ‖(4 : K)‖ ≤ 1 := norm_nat_le_one 4
  have hz2 : ‖z ^ 2‖ ≤ 1 := by
    simpa [norm_pow] using (pow_le_one₀ (norm_nonneg z) hz : ‖z‖ ^ 2 ≤ 1)
  calc
    ‖(6 : K) + 4 * z + z ^ 2‖ ≤ max (max ‖(6 : K)‖ ‖(4 : K) * z‖) ‖z ^ 2‖ := by
      exact (norm_add_bound _ _).trans (max_le_max_right _ (norm_add_bound _ _))
    _ ≤ 1 := by
      apply max_le (max_le h6 ?_) hz2
      rw [norm_mul]
      calc
        ‖(4 : K)‖ * ‖z‖ ≤ (1 : ℝ) * 1 :=
          mul_le_mul h4 hz (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _

private theorem norm_core_diff_le_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z w : K} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) : ‖(4 : K) + z + w‖ ≤ 1 := by
  have h4 : ‖(4 : K)‖ ≤ 1 := norm_nat_le_one 4
  calc
    ‖(4 : K) + z + w‖ ≤ max (max ‖(4 : K)‖ ‖z‖) ‖w‖ := by
      exact (norm_add_bound _ _).trans (max_le_max_right _ (norm_add_bound _ _))
    _ ≤ 1 := by exact max_le (max_le h4 hz) hw

private theorem norm_tail_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z : K} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r ≤ 1) :
    ‖z ^ 2 * ((6 : K) + 4 * z + z ^ 2)‖ ≤ r ^ 2 := by
  rw [norm_mul, norm_pow]
  calc
    ‖z‖ ^ 2 * ‖(6 : K) + 4 * z + z ^ 2‖ ≤ r ^ 2 * 1 := by
      exact mul_le_mul (by gcongr) (norm_core_le_one (hz.trans hr))
        (norm_nonneg _) (sq_nonneg _)
    _ = r ^ 2 := mul_one _

private theorem norm_tail_sub_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z w : K} {r : ℝ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖z ^ 2 * ((6 : K) + 4 * z + z ^ 2) -
      w ^ 2 * ((6 : K) + 4 * w + w ^ 2)‖ ≤ r * ‖z - w‖ := by
  have hsum : ‖z + w‖ ≤ r :=
    (norm_add_bound z w).trans (max_le hz hw)
  have hcorez : ‖(6 : K) + 4 * z + z ^ 2‖ ≤ 1 :=
    norm_core_le_one (hz.trans hr1)
  have hcoreDiff : ‖(4 : K) + z + w‖ ≤ 1 :=
    norm_core_diff_le_one (hz.trans hr1) (hw.trans hr1)
  have hw2 : ‖w‖ ^ 2 ≤ r ^ 2 := by gcongr
  have hr2 : r ^ 2 ≤ r := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hA : ‖(z - w) * (z + w) * ((6 : K) + 4 * z + z ^ 2)‖ ≤
      r * ‖z - w‖ := by
    rw [norm_mul, norm_mul]
    calc
      ‖z - w‖ * ‖z + w‖ * ‖(6 : K) + 4 * z + z ^ 2‖ ≤
          ‖z - w‖ * r * 1 := by gcongr
      _ = r * ‖z - w‖ := by ring
  have hB : ‖w ^ 2 * (z - w) * ((4 : K) + z + w)‖ ≤
      r * ‖z - w‖ := by
    rw [norm_mul, norm_mul, norm_pow]
    calc
      ‖w‖ ^ 2 * ‖z - w‖ * ‖(4 : K) + z + w‖ ≤
          r ^ 2 * ‖z - w‖ * 1 := by gcongr
      _ = r ^ 2 * ‖z - w‖ := by ring
      _ ≤ r * ‖z - w‖ := mul_le_mul_of_nonneg_right hr2 (norm_nonneg _)
  have hid : z ^ 2 * ((6 : K) + 4 * z + z ^ 2) -
      w ^ 2 * ((6 : K) + 4 * w + w ^ 2) =
      (z - w) * (z + w) * ((6 : K) + 4 * z + z ^ 2) +
      w ^ 2 * (z - w) * ((4 : K) + z + w) := by ring
  rw [hid]
  exact (norm_add_bound _ _).trans (max_le hA hB)

set_option linter.style.haveILetI false in
/-- A sufficiently small perturbation of one has a fourth root in a complete ultrametric
field. The condition is the Newton--Hensel bound at the approximate root `1`. -/
theorem exists_fourth_root_of_norm_sub_one_lt_norm_four_sq
    {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (u : K) (h4 : (4 : K) ≠ 0)
    (hu : ‖u - 1‖ < ‖(4 : K)‖ ^ 2) :
    ∃ y : K, y ^ 4 = u := by
  let c : ℝ := ‖(4 : K)‖
  have hcpos : 0 < c := norm_pos_iff.mpr h4
  have hcle1 : c ≤ 1 := norm_nat_le_one 4
  have hgap : ‖u - 1‖ / c < c := by
    apply (div_lt_iff₀ hcpos).2
    simpa only [c, pow_two, mul_comm] using hu
  obtain ⟨r, hrlow, hrhigh⟩ := exists_between hgap
  have hrpos : 0 < r :=
    lt_of_le_of_lt (div_nonneg (norm_nonneg _) hcpos.le) hrlow
  have hrle1 : r ≤ 1 := hrhigh.le.trans hcle1
  have hdelta : ‖u - 1‖ ≤ c * r := by
    exact ((div_lt_iff₀ hcpos).mp hrlow).le.trans_eq (mul_comm r c)
  have hr2 : r ^ 2 ≤ c * r := by
    simpa only [pow_two, mul_comm] using
      (mul_le_mul_of_nonneg_left hrhigh.le hrpos.le)
  let B : Set K := Metric.closedBall 0 r
  have memB (z : K) : z ∈ B ↔ ‖z‖ ≤ r := by
    simp [B, Metric.mem_closedBall, dist_eq_norm]
  letI : CompleteSpace B := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let f : B → B := fun z => ⟨(u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)) / 4,
    by
      have hz : ‖z.1‖ ≤ r := (memB z.1).mp z.2
      have htail := norm_tail_le hz hrle1
      apply (memB _).mpr
      rw [norm_div]
      apply (div_le_iff₀ hcpos).mpr
      change ‖u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)‖ ≤ r * c
      calc
        ‖u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)‖ ≤
            max ‖u - 1‖ ‖z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)‖ := by
          simpa only [sub_eq_add_neg, norm_neg] using
            (norm_add_bound (u - 1)
              (-(z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2))))
        _ ≤ c * r := max_le hdelta (htail.trans hr2)
        _ = r * c := mul_comm c r⟩
  let k : ℝ≥0 := Real.toNNReal (r / c)
  have hk_nonneg : 0 ≤ r / c := div_nonneg hrpos.le hcpos.le
  have hkcoe : (k : ℝ) = r / c := Real.coe_toNNReal (r / c) hk_nonneg
  have hk_lt : k < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one]
    rw [hkcoe]
    exact (div_lt_one hcpos).2 hrhigh
  have hf_lip : LipschitzWith k f := LipschitzWith.of_dist_le_mul fun z w => by
    have hz : ‖z.1‖ ≤ r := (memB z.1).mp z.2
    have hw : ‖w.1‖ ≤ r := (memB w.1).mp w.2
    have htail := norm_tail_sub_le hz hw hrpos.le hrle1
    have hid : ((u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)) / 4) -
        ((u - 1 - w.1 ^ 2 * ((6 : K) + 4 * w.1 + w.1 ^ 2)) / 4) =
        (w.1 ^ 2 * ((6 : K) + 4 * w.1 + w.1 ^ 2) -
          z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)) / 4 := by ring
    change dist (f z).1 (f w).1 ≤ (k : ℝ) * dist z.1 w.1
    rw [dist_eq_norm, dist_eq_norm]
    change ‖((u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)) / 4) -
      ((u - 1 - w.1 ^ 2 * ((6 : K) + 4 * w.1 + w.1 ^ 2)) / 4)‖ ≤
      (k : ℝ) * ‖z.1 - w.1‖
    rw [hid, norm_div, norm_sub_rev]
    calc
      ‖z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2) -
          w.1 ^ 2 * ((6 : K) + 4 * w.1 + w.1 ^ 2)‖ / c ≤
          (r * ‖z.1 - w.1‖) / c :=
        div_le_div_of_nonneg_right htail hcpos.le
      _ = (k : ℝ) * ‖z.1 - w.1‖ := by
        rw [hkcoe, div_eq_mul_inv]
        ring
  have hf : ContractingWith k f := ⟨hk_lt, hf_lip⟩
  have hzero : (0 : K) ∈ B := (memB 0).mpr (by simpa using hrpos.le)
  obtain ⟨z, hzfix, _, _⟩ := hf.exists_fixedPoint ⟨0, hzero⟩ (edist_ne_top _ _)
  refine ⟨1 + z.1, ?_⟩
  have hzval : (u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2)) / 4 = z.1 :=
    congrArg Subtype.val hzfix
  have hmul : u - 1 - z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2) =
      z.1 * 4 := (div_eq_iff h4).mp hzval
  calc
    (1 + z.1) ^ 4 = 1 + 4 * z.1 + z.1 ^ 2 * ((6 : K) + 4 * z.1 + z.1 ^ 2) := by ring
    _ = u := by linear_combination -hmul

end Erdos940.Quartic
