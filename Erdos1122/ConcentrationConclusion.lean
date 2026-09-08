import Erdos1122.Statements
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # The final deduction from finite concentration -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

/-- A density-zero set of decreases excludes negative support in any limiting
distribution of the increments. Continuity points suffice. -/
theorem limiting_increment_distribution_nonnegative (f : ℕ → ℝ) (F : ℝ → ℝ)
    (hF : IsLimitingDistribution (fun n => f (n + 1) - f n) F)
    (hdec : Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0)) :
    ∀ x : ℝ, x < 0 → F x = 0 := by
  obtain ⟨hmono, _hright, hbot, _htop, hdist⟩ := hF
  have hn (x : ℝ) : 0 ≤ F x := by
    apply le_of_tendsto hbot
    filter_upwards [eventually_le_atBot x] with y hy
    exact hmono hy
  have hc (y : ℝ) (hy : y < 0) (hcont : ContinuousAt F y) : F y = 0 := by
    have hz : Tendsto (fun X : ℝ =>
        (#{n ∈ Ioc 0 ⌊X⌋₊ | f (n + 1) - f n ≤ y} : ℝ) / X) atTop (𝓝 0) := by
      apply squeeze_zero' _ _ hdec
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        positivity
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        apply div_le_div_of_nonneg_right _ hX.le
        apply Nat.cast_le.2 (card_le_card ?_)
        intro n hnm
        obtain ⟨hn, hle⟩ := mem_filter.1 hnm
        exact mem_filter.2 ⟨hn, by linarith⟩
    exact tendsto_nhds_unique (hdist y hcont) hz
  intro x hx
  obtain ⟨y, hxy, hy⟩ := (hmono.countable_not_continuousAt.dense_compl ℝ).inter_open_nonempty
    (Set.Ioo x 0) isOpen_Ioo (Set.nonempty_Ioo.2 hx)
  have hcont : ContinuousAt F y := by simpa using hy
  exact le_antisymm ((hmono hxy.1.le).trans_eq (hc y hxy.2 hcont)) (hn x)

/-- The sign of the logarithmic coefficient follows from the same density
hypothesis, without a further number-theoretic input. -/
theorem logarithmic_coefficient_nonnegative (f : ℕ → ℝ) (c : ℝ)
    (hf : ∀ n : ℕ, 0 < n → f n = c * log n)
    (hdec : Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0)) : 0 ≤ c := by
  by_contra h
  have hc : c < 0 := lt_of_not_ge h
  have hd (n : ℕ) (hn : 0 < n) : f (n + 1) < f n := by
    rw [hf (n + 1) (by omega), hf n hn]
    apply mul_lt_mul_of_neg_left _ hc
    exact log_lt_log (by exact_mod_cast hn) (by exact_mod_cast Nat.lt_succ_self n)
  have he (X : ℝ) : decreaseCount f X = ⌊X⌋₊ := by
    unfold decreaseCount
    rw [filter_eq_self.2 (fun n hn => hd n (mem_Ioc.1 hn).1)]
    simp
  obtain ⟨X, hX, hsmall⟩ := ((eventually_ge_atTop (2 : ℝ)).and
    (hdec.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))).exists
  rw [he] at hsmall
  have hpos : 0 < X := by linarith
  have hh := (div_lt_iff₀ hpos).1 hsmall
  linarith [Nat.lt_floor_add_one X]

/-- The last implication in the manuscript. The distribution theorem remains
an explicit proposition hypothesis, and its source status is documented. -/
theorem logarithmic_of_finite_concentration (hV : ErdosV) (hX : ErdosX)
    (f : ℕ → ℝ) (hf : IsAdditive f) (hconc : FiniteConcentration f)
    (hdec : Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 0 < n → f n = c * log n := by
  obtain ⟨c, hc⟩ := (hV f hf).1 hconc
  obtain ⟨D, hdist, hchar⟩ := hX f hf c hc
  have hlog := hchar.1 (limiting_increment_distribution_nonnegative f D hdist hdec)
  exact ⟨c, logarithmic_coefficient_nonnegative f c hlog hdec, hlog⟩

end

end Erdos1122
