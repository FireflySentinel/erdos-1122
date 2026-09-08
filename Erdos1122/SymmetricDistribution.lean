import Erdos1122.HildebrandStatements
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Symmetric limiting laws supported on the nonnegative half-line -/

namespace Erdos1122

open Finset Real Filter Topology MeasureTheory ProbabilityTheory
open Statements

set_option autoImplicit false
noncomputable section

/-- Real characteristic functions are invariant under reflection. -/
theorem measure_reflection_of_real_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hreal : ∀ t : ℝ, (charFun μ t).im = 0) : μ.map (fun x => -x) = μ := by
  have : IsProbabilityMeasure (μ.map (fun x : ℝ => -x)) :=
    μ.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  funext t
  have he := charFun_map_mul (μ := μ) (-1) t
  simp only [neg_one_mul] at he
  rw [he, charFun_neg]
  apply Complex.ext <;> simp [hreal]

/-- No negative mass and reflection symmetry force a point mass at zero. -/
theorem eq_dirac_zero_of_symmetric_nonnegative (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x => -x) = μ)
    (hn : ∀ x : ℝ, x < 0 → cdf μ x = 0) : μ = Measure.dirac 0 := by
  have hz (x : ℝ) (hx : x < 0) : μ (Set.Iic x) = 0 := by
    rw [← ofReal_cdf, hn x hx]
    simp
  have hneg : μ (Set.Iio 0) = 0 := by
    have he := iUnion_Iic_eq_Iio_of_lt_of_tendsto
      (f := fun n : ℕ => -(1 / (n + 1 : ℝ))) (fun n => neg_lt_zero.2 (by positivity))
      (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg)
    rw [← he]
    exact measure_iUnion_null (fun n => hz _ (neg_lt_zero.2 (by positivity)))
  have hpos : μ (Set.Ioi 0) = 0 := by
    have hh := congrArg (fun ν : Measure ℝ => ν (Set.Iio 0)) hsym
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio] at hh
    simpa using hh.trans hneg
  have hae : (fun x : ℝ => x) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    apply ae_iff.2
    have he : {x : ℝ | ¬ x = 0} = Set.Iio 0 ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
      exact ne_iff_lt_or_gt
    rw [he]
    exact measure_union_null hneg hpos
  simpa using (Measure.map_congr hae)

theorem cdf_dirac_zero (x : ℝ) :
    cdf (Measure.dirac (0 : ℝ)) x = if 0 ≤ x then 1 else 0 := by
  rw [cdf_eq_real]
  by_cases h : 0 ≤ x <;> simp [measureReal_def, h]

theorem continuousAt_cdf_dirac_zero (x : ℝ) (hx : x ≠ 0) :
    ContinuousAt (cdf (Measure.dirac (0 : ℝ))) x := by
  by_cases hp : 0 < x
  · apply (continuousAt_const (y := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hp] with y hy
    simp [cdf_dirac_zero, hy.le]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hn] with y hy
    simp [cdf_dirac_zero, not_le_of_gt hy]

/-- A limiting point mass at zero gives density-zero exceptional sets for
each positive tolerance. -/
theorem tail_counts_tendsto_of_dirac_limit (g : ℕ → ℝ)
    (hD : IsLimitingDistribution g (cdf (Measure.dirac (0 : ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun X : ℝ => (#{n ∈ Ioc 0 ⌊X⌋₊ | ε < |g n|} : ℝ) / X) atTop (𝓝 0) := by
  classical
  have hm := hD.2.2.2.2 (-ε) (continuousAt_cdf_dirac_zero _ (by linarith))
  have hp := hD.2.2.2.2 ε (continuousAt_cdf_dirac_zero _ hε.ne')
  simp only [cdf_dirac_zero, show ¬ 0 ≤ -ε by linarith, if_false] at hm
  simp only [cdf_dirac_zero, if_pos hε.le] at hp
  have hf : Tendsto (fun X : ℝ => (⌊X⌋₊ : ℝ) / X) atTop (𝓝 1) := by
    simpa using tendsto_nat_floor_div_atTop
  have ht := hm.add (hf.sub hp)
  simp only [sub_self, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    let S := Ioc 0 ⌊X⌋₊
    have hin : S.filter (fun n => ε < |g n|) ⊆
        S.filter (fun n => g n ≤ -ε) ∪ S.filter (fun n => ¬ g n ≤ ε) := by
      intro n hn
      obtain ⟨hnS, hng⟩ := mem_filter.1 hn
      rcases (lt_abs.1 hng) with hp | hm
      · exact mem_union_right _ (mem_filter.2 ⟨hnS, not_le_of_gt hp⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hnS, by linarith⟩)
    have hh := (card_le_card hin).trans (card_union_le _ _)
    have he := card_filter_add_card_filter_not (s := S) (fun n => g n ≤ ε)
    have hc : (S.card : ℝ) = ⌊X⌋₊ := by simp [S]
    have hhR : ((S.filter (fun n => ε < |g n|)).card : ℝ) ≤
        ((S.filter (fun n => g n ≤ -ε)).card : ℝ) +
          ((S.filter (fun n => ¬ g n ≤ ε)).card : ℝ) := by exact_mod_cast hh
    have heR : ((S.filter (fun n => g n ≤ ε)).card : ℝ) +
        ((S.filter (fun n => ¬ g n ≤ ε)).card : ℝ) = (⌊X⌋₊ : ℝ) := by
      rw [← hc]
      exact_mod_cast he
    have hb := div_le_div_of_nonneg_right (show ((S.filter (fun n => ε < |g n|)).card : ℝ) ≤
      ((S.filter (fun n => g n ≤ -ε)).card : ℝ) + (⌊X⌋₊ : ℝ) -
        ((S.filter (fun n => g n ≤ ε)).card : ℝ) by linarith) hX.le
    simpa only [add_div, sub_div, add_sub_assoc, S] using hb

end

end Erdos1122
