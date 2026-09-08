import Erdos1122.ConcentrationConclusion
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Identifying the coefficient of a logarithm -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

/-- A logarithm can have a summable truncated residual only at its own coefficient. -/
theorem logarithmic_coefficient_unique (f : ℕ → ℝ) (c d : ℝ)
    (hf : ∀ n : ℕ, 0 < n → f n = d * log n)
    (hc : TruncatedPrimeSummable f c) : d = c := by
  by_contra hdc
  let a := min ((d - c) ^ 2 * (log 2) ^ 2) 1
  have ha : 0 < a := lt_min (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.2 hdc))
    (sq_pos_of_pos (log_pos (by norm_num : (1 : ℝ) < 2)))) zero_lt_one
  have hh : Summable (fun p : Nat.Primes => a / (p.val : ℝ)) := by
    apply hc.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      have hlog : log 2 ≤ log p.val := log_le_log (by norm_num)
        (by exact_mod_cast p.property.two_le)
      have hp := pow_le_pow_left₀ (log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) hlog 2
      have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg (d - c))
      have he : f p.val - c * log p.val = (d - c) * log p.val := by
        rw [hf p.val p.property.pos]
        ring
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [he, mul_pow]
      exact min_le_min hmul le_rfl
  have hrec := hh.mul_left a⁻¹
  apply Nat.Primes.not_summable_one_div
  simpa only [← mul_div_assoc, inv_mul_cancel₀ ha.ne'] using hrec

/-- Ordinary convergence to zero excludes negative support in any limiting law. -/
theorem limiting_distribution_nonnegative_of_tendsto (g : ℕ → ℝ) (F : ℝ → ℝ)
    (hF : IsLimitingDistribution g F) (hg : Tendsto g atTop (𝓝 0)) :
    ∀ x : ℝ, x < 0 → F x = 0 := by
  obtain ⟨hmono, _hright, hbot, _htop, hdist⟩ := hF
  have hn (x : ℝ) : 0 ≤ F x := by
    apply le_of_tendsto hbot
    filter_upwards [eventually_le_atBot x] with y hy
    exact hmono hy
  have hc (y : ℝ) (hy : y < 0) (hcont : ContinuousAt F y) : F y = 0 := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hg.eventually (eventually_gt_nhds hy))
    have hz : Tendsto (fun X : ℝ => (#{n ∈ Ioc 0 ⌊X⌋₊ | g n ≤ y} : ℝ) / X)
        atTop (𝓝 0) := by
      apply squeeze_zero' _ _ (tendsto_id.const_div_atTop (N : ℝ))
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        positivity
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        apply div_le_div_of_nonneg_right _ hX.le
        have hin : (Ioc 0 ⌊X⌋₊).filter (fun n => g n ≤ y) ⊆ Ioc 0 N := by
          intro n hn
          obtain ⟨hnX, hny⟩ := mem_filter.1 hn
          have hlt : n < N := by
            by_contra hh
            exact (not_le_of_gt (hN n (le_of_not_gt hh))) hny
          exact mem_Ioc.2 ⟨(mem_Ioc.1 hnX).1, hlt.le⟩
        exact_mod_cast (by simpa using card_le_card hin :
          ((Ioc 0 ⌊X⌋₊).filter (fun n => g n ≤ y)).card ≤ N)
    exact tendsto_nhds_unique (hdist y hcont) hz
  intro x hx
  obtain ⟨y, hxy, hy⟩ := (hmono.countable_not_continuousAt.dense_compl ℝ).inter_open_nonempty
    (Set.Ioo x 0) isOpen_Ioo (Set.nonempty_Ioo.2 hx)
  have hcont : ContinuousAt F y := by simpa using hy
  exact le_antisymm ((hmono hxy.1.le).trans_eq (hc y hxy.2 hcont)) (hn x)

theorem logarithmic_increments_tendsto (f : ℕ → ℝ) (c : ℝ)
    (hf : ∀ n : ℕ, 0 < n → f n = c * log n) :
    Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0) := by
  have h := tendsto_log_nat_add_one_sub_log.const_mul c
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [hf n hn, hf (n + 1) (by omega), Nat.cast_add, Nat.cast_one, mul_sub]

end

end Erdos1122
