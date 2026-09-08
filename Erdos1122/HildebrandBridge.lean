import Erdos1122.SymmetricDistribution
import Erdos1122.DensityOne
import Erdos1122.LogarithmicRigidity

/-! # Hildebrand's proved results imply the required Erdős X statement

The Euler factors in (1.4) are real. Uniqueness of characteristic functions
therefore gives reflection symmetry. A symmetric law with no negative mass
is concentrated at zero; the density-one extraction supplies the exact
hypothesis of Hildebrand's corollary. The logarithmic coefficient is then
identified by divergence of the reciprocal-prime series.
-/

namespace Erdos1122

open Finset Real Filter Topology MeasureTheory ProbabilityTheory
open Statements

set_option autoImplicit false
noncomputable section

/-- Formula (1.4) forces the limiting law to be symmetric. -/
theorem hildebrand_limiting_law_symmetric (hH : HildebrandTheorem)
    (f : ℕ → ℝ) (hf : IsAdditive f) (c : ℝ) (hc : TruncatedPrimeSummable f c)
    (μ : ProbabilityMeasure ℝ)
    (hD : IsLimitingDistribution (fun n => f (n + 1) - f n) (cdf (μ : Measure ℝ))) :
    (μ : Measure ℝ).map (fun x => -x) = μ := by
  apply measure_reflection_of_real_charFun
  intro t
  have hprod := (hH f hf).2 μ hD c hc t
  have hh := Complex.continuous_im.tendsto (charFun (μ : Measure ℝ) t) |>.comp hprod
  simp only [Function.comp_def, Complex.ofReal_im] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

/-- The announced Erdős X input is discharged using Hildebrand Theorem 1
and its proved density-one corollary. -/
theorem hildebrand_implies_erdosX (hH : Hildebrand) : ErdosX := by
  intro f hf c hc
  obtain ⟨μ, hD⟩ := (hH.1 f hf).1.2 ⟨c, hc⟩
  have hsym := hildebrand_limiting_law_symmetric hH.1 f hf c hc μ hD
  refine ⟨cdf (μ : Measure ℝ), hD, ?_⟩
  constructor
  · intro hn
    have he := eq_dirac_zero_of_symmetric_nonnegative (μ : Measure ℝ) hsym hn
    rw [he] at hD
    have hdens := density_one_zero_of_tail_counts _ (tail_counts_tendsto_of_dirac_limit _ hD)
    obtain ⟨d, hd⟩ := hH.2 f hf hdens
    have hdc := logarithmic_coefficient_unique f c d hd hc
    simpa only [hdc] using hd
  · intro hlog
    exact limiting_distribution_nonnegative_of_tendsto _ _ hD
      (logarithmic_increments_tendsto f c hlog)

end

end Erdos1122
