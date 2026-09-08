import Erdos1122.HildebrandStatements

/-! # From exceptional-set densities to a density-one set

Choose a cutoff for each tolerance. The exceptional sets are nested, so at
each finite endpoint their union is controlled by the last active tolerance.
This proves the actual hypothesis of Hildebrand's corollary.
-/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

/-- Statistical convergence to zero admits a single density-one set on which
the ordinary limit is zero. -/
theorem density_one_zero_of_tail_counts (g : ℕ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun X : ℝ =>
      (#{n ∈ Ioc 0 ⌊X⌋₊ | ε < |g n|} : ℝ) / X) atTop (𝓝 0)) :
    DensityOneZero g := by
  classical
  have hc (k : ℕ) : ∃ N : ℕ, k ≤ N ∧ ∀ X : ℝ, (N : ℝ) ≤ X →
      (#{n ∈ Ioc 0 ⌊X⌋₊ | 1 / (k + 1 : ℝ) < |g n|} : ℝ) / X ≤ 1 / (k + 1 : ℝ) := by
    have hp : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨B, hB⟩ := eventually_atTop.1 ((h _ hp).eventually (eventually_le_nhds hp))
    refine ⟨max k ⌈B⌉₊, le_max_left _ _, fun X hX => hB X ?_⟩
    have hmax : (⌈B⌉₊ : ℝ) ≤ (max k ⌈B⌉₊ : ℕ) := by
      exact_mod_cast le_max_right k ⌈B⌉₊
    exact (Nat.le_ceil B).trans (hmax.trans hX)
  choose N hNk hN using hc
  let S : Set ℕ := {n | ∀ k : ℕ, N k ≤ n → |g n| ≤ 1 / (k + 1 : ℝ)}
  refine ⟨S, ?_, ?_⟩
  · apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop (N K : ℝ), eventually_gt_atTop (0 : ℝ)] with X hX hX0
    let T := (range (⌊X⌋₊ + 1)).filter (fun k => N k ≤ ⌊X⌋₊)
    have hKT : K ∈ T := by
      have hh : N K ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX0.le).2 hX
      exact mem_filter.2 ⟨mem_range.2 (by have := hNk K; omega), hh⟩
    let k := T.max' ⟨K, hKT⟩
    have hkT : k ∈ T := T.max'_mem _
    have hKk : K ≤ k := T.le_max' K hKT
    have hkX : (N k : ℝ) ≤ X :=
      (Nat.le_floor_iff hX0.le).1 (mem_filter.1 hkT).2
    have hsub : (Ioc 0 ⌊X⌋₊).filter (fun n => n ∉ S) ⊆
        (Ioc 0 ⌊X⌋₊).filter (fun n => 1 / (k + 1 : ℝ) < |g n|) := by
      intro n hn
      obtain ⟨hnX, hnS⟩ := mem_filter.1 hn
      change ¬ ∀ j : ℕ, N j ≤ n → |g n| ≤ 1 / (j + 1 : ℝ) at hnS
      push Not at hnS
      obtain ⟨j, hjn, hjg⟩ := hnS
      have hjT : j ∈ T := mem_filter.2 ⟨mem_range.2
        (by have := hNk j; have := (mem_Ioc.1 hnX).2; omega), hjn.trans (mem_Ioc.1 hnX).2⟩
      have hjk : j ≤ k := T.le_max' j hjT
      have hr : 1 / (k + 1 : ℝ) ≤ 1 / (j + 1 : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
      exact mem_filter.2 ⟨hnX, hr.trans_lt hjg⟩
    have hh := (div_le_div_of_nonneg_right (Nat.cast_le.2 (card_le_card hsub)) hX0.le).trans (hN k X hkX)
    have hr : 1 / (k + 1 : ℝ) ≤ 1 / (K + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hKk 1)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    exact hh.trans_lt (hr.trans_lt hK)
  · apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    apply eventually_inf_principal.2
    filter_upwards [eventually_ge_atTop (N K)] with n hn hnS
    rw [Real.dist_eq, sub_zero]
    exact (hnS K hn).trans_lt hK

end

end Erdos1122
