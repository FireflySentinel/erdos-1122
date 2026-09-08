import Erdos1122.ComparisonFamily
import Erdos1122.ConcentrationConclusion
import Erdos1122.NormalizedExistence
import Erdos1122.MixedMoment
import Erdos1122.VarianceLower
import Erdos1122.ClippedComparison
import Erdos1122.WindowAssembly

/-! # The main implication from the five cited theorems

The proof chooses all constants before the cutoff limits, applies the actual
short-interval theorem to the clipped prime-divisor family, obtains finite
concentration by contradiction, and concludes with the cited distribution
statement. Every intermediate arithmetic proposition is discharged by a theorem.
-/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

/-- The entire chain to Erdős Problem 1122, conditional on exactly the
five cited theorems. No intermediate arithmetic hypothesis remains. -/
theorem Statements.main_of_cited
    (hM : Mangerel) (hR : Ruzsa) (hE : Elliott) (hV : ErdosV) (hX : ErdosX) :
    ErdosProblem1122 := by
  intro f hf hdec
  apply logarithmic_of_finite_concentration hV hX f hf _ hdec
  by_contra hno
  obtain ⟨c₀, C₀, hc₀, _hC₀, hlower⟩ := projection_instance hR
  obtain ⟨C, _hC, hupper⟩ := clipped_comparison hE (estimate55_of_ruzsa hR)
  obtain ⟨K, M, hK, hMpos, hquarter, hstrict⟩ := choose_constants c₀ C₀ (8 * C) hc₀
  obtain ⟨N⟩ := normalization_exists hV f hf hno M hMpos
  obtain ⟨hvarBound, hlow⟩ := hlower f hf K M hK hMpos hquarter N
  obtain ⟨herrBound, herr⟩ := hupper f hf K M hK hMpos hquarter N
  have hshort := N.comparison_short_intervals hM hE K hK hMpos
  have hcomp := window_assembly_of_elliott hE f hf hdec K M hK hMpos hquarter N herrBound hshort
  have hnonneg (X : ℝ) : 0 ≤ N.variance K X :=
    initialMean_square_nonneg (fun n => N.comparison K X n - primeCenter (N.comparison K X) X) X
  have hbelow : IsBoundedUnder (· ≥ ·) atTop (N.variance K) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ X : ℝ in atTop, 0 ≤ N.variance K X
    exact Eventually.of_forall hnonneg
  have hlims := liminf_le_limsup hvarBound hbelow
  have hgap := hlow.trans (hlims.trans (hcomp.trans
    (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8))))
  have he : 8 * (C * (M / K ^ 2 + M ^ 2 * log (2 / M) + K ^ 2 * M ^ 2)) =
      (8 * C) * M / K ^ 2 + (8 * C) * M ^ 2 * log (2 / M) +
        (8 * C) * K ^ 2 * M ^ 2 := by ring
  rw [he] at hgap
  exact (not_lt_of_ge hgap) hstrict

end

end Erdos1122
