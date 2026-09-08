import Erdos1122.Constants
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Ordered limits and the final variance comparison

All analytic estimates are hypotheses. The order of the filters is part of
each statement; no exchange of limits or uniformity in a moving parameter
is assumed implicitly.
-/

namespace Erdos1122

open Filter Topology

noncomputable section

variable {α : Type*} [Preorder α] [NeBot (atTop : Filter α)]

theorem limsup_nonneg {u : α → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hb : IsBoundedUnder (· ≤ ·) atTop u) : 0 ≤ limsup u atTop := by
  apply le_limsup_of_le hb
  intro b h
  obtain ⟨n, hn⟩ := h.exists
  exact (hu n).trans hn

/-- The finite four-term inequality, followed by the limit in `X` for fixed `H`. -/
theorem four_term_limsup_bound
    (A E V S B : α → ℝ) (hA : ∀ X, 0 ≤ A X)
    (hE : IsBoundedUnder (· ≤ ·) atTop E)
    (hS : IsBoundedUnder (· ≤ ·) atTop S)
    (hV : Tendsto V atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 0))
    (hcomp : ∀ᶠ X in atTop, A X ≤ 8 * E X + 4 * V X + 4 * S X + B X) :
    limsup A atTop ≤ 8 * limsup E atTop + 4 * limsup S atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε / 17 := by positivity
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop hA)
  filter_upwards [hcomp,
    eventually_lt_of_limsup_lt (show limsup E atTop < limsup E atTop + ε / 17 by linarith) hE,
    eventually_lt_of_limsup_lt (show limsup S atTop < limsup S atTop + ε / 17 by linarith) hS,
    hV.eventually (eventually_lt_nhds hδ),
    hB.eventually (eventually_lt_nhds hδ)] with X hc he hs hv hb
  linarith

/-- First `X → ∞` at fixed `H`, then `H → ∞`. The endpoint term is `B`. -/
theorem variance_limsup_bound
    (A E : α → ℝ) (V S B : ℕ → α → ℝ) (hA : ∀ X, 0 ≤ A X)
    (hE : IsBoundedUnder (· ≤ ·) atTop E)
    (hS : ∀ H, 0 < H → IsBoundedUnder (· ≤ ·) atTop (S H))
    (hV : ∀ H, 0 < H → Tendsto (V H) atTop (𝓝 0))
    (hB : ∀ H, 0 < H → Tendsto (B H) atTop (𝓝 0))
    (hshort : Tendsto (fun H => limsup (S H) atTop) atTop (𝓝 0))
    (hcomp : ∀ H, 0 < H → ∀ᶠ X in atTop,
      A X ≤ 8 * E X + 4 * V H X + 4 * S H X + B H X) :
    limsup A atTop ≤ 8 * limsup E atTop := by
  have hlim : Tendsto (fun H => 8 * limsup E atTop + 4 * limsup (S H) atTop)
      atTop (𝓝 (8 * limsup E atTop)) := by
    simpa using tendsto_const_nhds.add (hshort.const_mul 4)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  exact four_term_limsup_bound A E (V H) (S H) (B H) hA hE
    (hS H hH) (hV H hH) (hB H hH) (hcomp H hH)

/-- The `X`, `H`, and small-tail limits used in extending dyadic bands to a full interval.
For each fixed positive `η`, the band error tends to zero only as `H → ∞`.
Its rate may depend on `η`. -/
theorem iterated_limsup_zero
    (F : ℕ → α → ℝ) (band : ℝ → ℕ → ℝ) (tail : ℝ → ℝ)
    (hF : ∀ H X, 0 ≤ F H X)
    (hbounded : ∀ H, IsBoundedUnder (· ≤ ·) atTop (F H))
    (hband : ∀ η, 0 < η → Tendsto (band η) atTop (𝓝 0))
    (htail : Tendsto tail (𝓝[>] 0) (𝓝 0))
    (hcover : ∀ η, 0 < η → ∀ᶠ H in atTop,
      limsup (F H) atTop ≤ band η H + tail η) :
    Tendsto (fun H => limsup (F H) atTop) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun H => ha.trans_le (limsup_nonneg (hF H) (hbounded H))
  · intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    obtain ⟨η, hη, hsmall⟩ := ((show ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η from self_mem_nhdsWithin).and
      (htail.eventually (eventually_lt_nhds hhalf))).exists
    filter_upwards [hcover η hη,
      (hband η hη).eventually (eventually_lt_nhds hhalf)] with H hc hb
    linarith

/-- Once the two variance bounds hold for every fixed `K,M`, they are incompatible.
The witnesses are chosen before either bound is instantiated. -/
theorem variance_bounds_contradict (c₀ C₀ C₁ : ℝ) (hc₀ : 0 < c₀)
    (v : ℝ → ℝ → ℝ)
    (hlower : ∀ K M, 1 < K → 0 < M → M < 1 / 4 →
      c₀ * M - C₀ * K ^ 2 * M ^ 2 ≤ v K M)
    (hupper : ∀ K M, 1 < K → 0 < M → M < 1 / 4 →
      v K M ≤ C₁ * M / K ^ 2 + C₁ * M ^ 2 * Real.log (2 / M) + C₁ * K ^ 2 * M ^ 2) :
    False := by
  obtain ⟨K, M, hK, hM, hquarter, hstrict⟩ := choose_constants c₀ C₀ C₁ hc₀
  exact (not_lt_of_ge ((hlower K M hK hM hquarter).trans
    (hupper K M hK hM hquarter))) hstrict

end

end Erdos1122
