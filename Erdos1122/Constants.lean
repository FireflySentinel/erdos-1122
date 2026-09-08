import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # The ordered choice of constants in the final contradiction -/

namespace Erdos1122

open Filter Topology

noncomputable section

theorem tendsto_mul_log_two_div :
    Tendsto (fun M : ℝ => M * Real.log (2 / M)) (𝓝[>] 0) (𝓝 0) := by
  have hm : Tendsto (fun M : ℝ => M) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlog : Tendsto (fun M : ℝ => Real.log M * M) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have h := (hm.mul_const (Real.log 2)).sub hlog
  simp only [zero_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with M hM
  rw [Real.log_div (by norm_num) (ne_of_gt hM)]
  ring

/-- `K` is fixed first; the inequality then holds for every sufficiently small positive `M`.
The constants `C₀` and `C₁` need not be positive. -/
theorem choose_constants_eventually (c₀ C₀ C₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ K : ℝ, 1 < K ∧ ∀ᶠ M : ℝ in 𝓝[>] 0,
      0 < M ∧ M < 1 / 4 ∧
      C₁ * M / K ^ 2 + C₁ * M ^ 2 * Real.log (2 / M) + C₁ * K ^ 2 * M ^ 2
        < c₀ * M - C₀ * K ^ 2 * M ^ 2 := by
  have hk : Tendsto (fun K : ℝ => C₁ / K ^ 2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).const_div_atTop C₁
  obtain ⟨K, hK, hsmall⟩ := ((eventually_gt_atTop (1 : ℝ)).and
    (hk.eventually (eventually_lt_nhds (show (0 : ℝ) < c₀ / 4 by positivity)))).exists
  refine ⟨K, hK, ?_⟩
  have hm : Tendsto (fun M : ℝ => M) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun M : ℝ => C₁ / K ^ 2 + C₁ * (M * Real.log (2 / M)) +
        (C₁ + C₀) * K ^ 2 * M) (𝓝[>] 0) (𝓝 (C₁ / K ^ 2)) := by
    convert! (tendsto_const_nhds.add (tendsto_mul_log_two_div.const_mul C₁)).add
      (hm.const_mul ((C₁ + C₀) * K ^ 2)) using 1
    simp
  have hlt : C₁ / K ^ 2 < c₀ := by linarith
  filter_upwards [self_mem_nhdsWithin,
    hm.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
    hlim.eventually (eventually_lt_nhds hlt)] with M hM hquarter hbound
  refine ⟨hM, hquarter, ?_⟩
  have hprod := mul_lt_mul_of_pos_right hbound hM
  rw [lt_sub_iff_add_lt]
  convert! hprod using 1
  ring

theorem choose_constants (c₀ C₀ C₁ : ℝ) (hc₀ : 0 < c₀) :
    ∃ K M : ℝ, 1 < K ∧ 0 < M ∧ M < 1 / 4 ∧
      C₁ * M / K ^ 2 + C₁ * M ^ 2 * Real.log (2 / M) + C₁ * K ^ 2 * M ^ 2
        < c₀ * M - C₀ * K ^ 2 * M ^ 2 := by
  obtain ⟨K, hK, hM⟩ := choose_constants_eventually c₀ C₀ C₁ hc₀
  obtain ⟨M, hM⟩ := hM.exists
  exact ⟨K, M, hK, hM⟩

end

end Erdos1122
