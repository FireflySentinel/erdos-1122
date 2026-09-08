import Erdos1122.ClippedComparison

/-! # The density hypothesis gives small variation of the clipped observable -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

theorem clip_negative_increment_le (K x y r : ℝ) (hr : 0 ≤ r) (hxy : x - y ≤ r) :
    max (clip K x - clip K y) 0 ≤ r := by
  apply max_le _ hr
  by_cases h : x ≤ y
  · exact (sub_nonpos.2 (clip_monotone K h)).trans hr
  · have hh := clip_lipschitz K x y
    rw [abs_of_nonneg (sub_nonneg.2 (le_of_not_ge h))] at hh
    exact (le_abs_self _).trans (hh.trans hxy)

theorem sum_log_increment (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (log ((n : ℝ) + 1) - log n)) = log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (by omega), ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- The zero index is accounted for separately; `D_f(X)` counts exactly
the positive indices in its definition. -/
theorem observable_variation_bound (f : ℕ → ℝ) (X K s c a : ℝ)
    (hK : 0 ≤ K) (hs : 0 < s) :
    totalVariation (fun n => clip K (f n / s - c * log n - a)) (⌊X⌋₊ + 1) ≤
      6 * K + 4 * K * (decreaseCount f X : ℝ) + 2 * |c| * log ((⌊X⌋₊ : ℝ) + 1) := by
  let Y := fun n => clip K (f n / s - c * log n - a)
  let e := fun n => if n = 0 then 2 * K else
    2 * K * (if f (n + 1) < f n then 1 else 0) + |c| * (log ((n : ℝ) + 1) - log n)
  have hneg (n : ℕ) (_hn : n < ⌊X⌋₊ + 1) : max (Y n - Y (n + 1)) 0 ≤ e n := by
    have hy (m : ℕ) : |Y m| ≤ K := abs_clip_le hK _
    by_cases hn : n = 0
    · subst n
      dsimp [e]
      exact max_le (by linarith [(abs_le.1 (hy 0)).2, (abs_le.1 (hy 1)).1]) (by positivity)
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hlog : 0 ≤ log ((n : ℝ) + 1) - log n := sub_nonneg.2 (log_le_log hn0 (by linarith))
      dsimp [e]
      rw [if_neg hn]
      by_cases hd : f (n + 1) < f n
      · rw [if_pos hd, mul_one]
        apply max_le _ (by positivity)
        linarith [(abs_le.1 (hy n)).2, (abs_le.1 (hy (n + 1))).1, mul_nonneg (abs_nonneg c) hlog]
      · rw [if_neg hd, mul_zero, zero_add]
        apply clip_negative_increment_le _ _ _ _ (mul_nonneg (abs_nonneg c) hlog)
        have hf := div_le_div_of_nonneg_right (le_of_not_gt hd) hs.le
        have hc := mul_le_mul_of_nonneg_right (le_abs_self c) hlog
        simp only [Nat.cast_add, Nat.cast_one]
        nlinarith only [hf, hc]
  have hv := total_variation_le Y e (⌊X⌋₊ + 1) K (abs_clip_le hK _) (abs_clip_le hK _) hneg
  have he : range (⌊X⌋₊ + 1) = insert 0 (Ioc 0 ⌊X⌋₊) := by
    ext n
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  have he0 : e 0 = 2 * K := by simp [e]
  have hesum : (∑ n ∈ range (⌊X⌋₊ + 1), e n) =
      2 * K + 2 * K * (decreaseCount f X : ℝ) + |c| * log ((⌊X⌋₊ : ℝ) + 1) := by
    rw [he, sum_insert (by simp), he0]
    have ht : (∑ n ∈ Ioc 0 ⌊X⌋₊, e n) =
        2 * K * (decreaseCount f X : ℝ) + |c| * log ((⌊X⌋₊ : ℝ) + 1) := by
      calc
        _ = ∑ n ∈ Ioc 0 ⌊X⌋₊,
            (2 * K * (if f (n + 1) < f n then 1 else 0) + |c| * (log ((n : ℝ) + 1) - log n)) := by
          apply sum_congr rfl
          intro n hn
          dsimp [e]
          rw [if_neg (Nat.ne_of_gt (mem_Ioc.1 hn).1)]
        _ = _ := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_log_increment]
          simp [decreaseCount]
    rw [ht]
    ring
  rw [hesum] at hv
  exact hv.trans_eq (by ring)

theorem log_floor_ratio_tendsto_zero :
    Tendsto (fun X : ℝ => log ((⌊X⌋₊ : ℝ) + 1) / X) atTop (𝓝 0) := by
  have hb : Tendsto (fun X : ℝ => (log 2 + log X) / X) atTop (𝓝 0) := by
    simpa only [add_div, zero_add, id_eq] using
      (tendsto_id.const_div_atTop (log (2 : ℝ))).add isLittleO_log_id_atTop.tendsto_div_nhds_zero
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_nonneg (log_nonneg (by have := Nat.cast_nonneg (α := ℝ) ⌊X⌋₊; linarith)) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    apply div_le_div_of_nonneg_right _ (by linarith)
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : X ≠ 0)]
    exact log_le_log (by positivity) (by linarith [Nat.floor_le (show 0 ≤ X by linarith)])

namespace NormalizedFamily

variable {f : ℕ → ℝ} {M : ℝ}

theorem observable_variation_tendsto (N : NormalizedFamily f M) (K : ℝ) (hK : 0 ≤ K)
    (hdec : Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0)) :
    Tendsto (fun X : ℝ => totalVariation (N.observable K X) (⌊X⌋₊ + 1) / X) atTop (𝓝 0) := by
  have hb : Tendsto (fun X : ℝ => (6 * K + 4 * K * (decreaseCount f X : ℝ) +
      2 * |N.slope X| * log ((⌊X⌋₊ : ℝ) + 1)) / X) atTop (𝓝 0) := by
    convert! ((tendsto_id.const_div_atTop (6 * K)).add (hdec.const_mul (4 * K))).add
      ((N.slope_tendsto.abs.const_mul 2).mul log_floor_ratio_tendsto_zero) using 1
    · ext X
      dsimp
      ring
    · simp
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_nonneg (totalVariation_nonneg _ _) (by linarith)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_le_div_of_nonneg_right
      (observable_variation_bound f X K (N.scale X) (N.slope X) (N.offset X) hK (N.scale_pos X))
      (by linarith)

def observableWindowMoment (N : NormalizedFamily f M) (K : ℝ) (H : ℕ) (X : ℝ) : ℝ :=
  (∑ n ∈ Icc H ⌊X⌋₊, (N.observable K X n - backwardWindowAverage H (N.observable K X) n) ^ 2) / X

theorem observable_window_tendsto (N : NormalizedFamily f M) (K : ℝ) (hK : 0 ≤ K)
    (hdec : Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0))
    (H : ℕ) (hH : 0 < H) : Tendsto (N.observableWindowMoment K H) atTop (𝓝 0) := by
  have ht : Tendsto (fun X : ℝ => 2 * K * (H : ℝ) *
      (totalVariation (N.observable K X) (⌊X⌋₊ + 1) / X)) atTop (𝓝 0) := by
    simpa using (N.observable_variation_tendsto K hK hdec).const_mul (2 * K * (H : ℝ))
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (by linarith)
  · filter_upwards [eventually_ge_atTop (H : ℝ), eventually_ge_atTop (1 : ℝ)] with X hHX hX
    have hHN : H ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).2 hHX
    have he : ⌊X⌋₊ + 1 - H + H = ⌊X⌋₊ + 1 := by omega
    have hh := sum_square_backward_discrepancy_le (N.observable K X) (⌊X⌋₊ + 1 - H) H hH K hK
      (fun _ _ => abs_clip_le hK _)
    rw [he] at hh
    have hsum : (∑ n ∈ Icc H ⌊X⌋₊,
        (N.observable K X n - backwardWindowAverage H (N.observable K X) n) ^ 2) =
        ∑ n ∈ range (⌊X⌋₊ + 1 - H),
          (N.observable K X (H + n) - backwardWindowAverage H (N.observable K X) (H + n)) ^ 2 := by
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    unfold observableWindowMoment
    rw [hsum]
    exact (div_le_div_of_nonneg_right hh (by linarith : 0 ≤ X)).trans_eq (by ring)

end NormalizedFamily

end

end Erdos1122
