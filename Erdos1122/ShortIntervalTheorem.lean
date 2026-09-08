import Erdos1122.DyadicCover

/-! # Lemma 2.1, conditional only on Mangerel

The family may vary with the real cutoff. The limit in that cutoff is taken
first, with the integer window held fixed throughout each inner limit.
-/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

/-- The complete short-interval conclusion from Mangerel, including the
fourth-moment, covering, and center-error estimates. -/
theorem short_interval_second_moment (hM : Mangerel)
    (z : ℝ → ℕ → ℝ) (L V : ℝ) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hz : ∀ X, IsStronglyAdditive (z X))
    (hcoeff : ∀ X p, p.Prime → |z X p| ≤ L)
    (hmass : ∀ X, 2 ≤ X → primeMoment (z X) X 2 ≤ V) :
    Tendsto (fun H : ℕ => limsup (fun X : ℝ => shortIntervalMoment H (z X) X 2) atTop)
      atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  obtain ⟨C, hC, hfourth⟩ := stronglyAdditive_fourth_moment L V hL hV
  let F : ℕ → ℝ → ℝ := fun H X => shortIntervalMoment (H + 1) (z X) X 2
  let band : ℕ → ℕ → ℝ → ℝ := fun j H X =>
    dyadicSecondMoment (H + 1) (z X) (dyadicRatio j * X)
  have h4 (H : ℕ) : ∀ᶠ X : ℝ in atTop, shortIntervalMoment (H + 1) (z X) X 4 ≤ C := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    exact shortInterval_fourth_bound H (z X) X C (by linarith)
      (hfourth (z X) (hz X) X hX (fun p hp => hcoeff X p (Nat.prime_of_mem_primesLE hp)) (hmass X hX))
  have hFn (H : ℕ) (X : ℝ) : 0 ≤ F H X := shortIntervalMoment_nonneg H (z X) X
  have hFb (H : ℕ) : IsBoundedUnder (· ≤ ·) atTop (F H) := by
    refine ⟨C + 1, ?_⟩
    change ∀ᶠ X : ℝ in atTop, F H X ≤ C + 1
    filter_upwards [h4 H, eventually_gt_atTop (0 : ℝ)] with X hh hX
    exact shortInterval_second_bound H (z X) X C hX hh
  have hBb (j H : ℕ) : IsBoundedUnder (· ≤ ·) atTop (band j H) := by
    refine ⟨2 * (2 * C) + 1, ?_⟩
    change ∀ᶠ X : ℝ in atTop, band j H X ≤ 2 * (2 * C) + 1
    have hscale : Tendsto (fun X : ℝ => dyadicRatio j * X) atTop atTop :=
      tendsto_id.const_mul_atTop (dyadicRatio_pos j)
    filter_upwards [hscale.eventually (eventually_ge_atTop (max 2 (100 * ((H + 1 : ℕ) : ℝ)))),
      eventually_ge_atTop (2 : ℝ)] with X hY hX
    have hY2 : 2 ≤ dyadicRatio j * X := (le_max_left _ _).trans hY
    have hHY : ((H + 1 : ℕ) : ℝ) ≤ (dyadicRatio j * X) / 100 := by
      linarith [le_max_right 2 (100 * ((H + 1 : ℕ) : ℝ))]
    have hh := dyadic_centered_fourth_bound (z X) (dyadicRatio j * X) (H + 1)
      hY2 (by omega) hHY C
      (hfourth (z X) (hz X) (dyadicRatio j * X) hY2
        (fun p hp => hcoeff X p (Nat.prime_of_mem_primesLE hp))
        ((primeMoment_mono (z X) 2 (mul_le_of_le_one_left (by linarith) (dyadicRatio_le_one j))).trans (hmass X hX)))
    exact weighted_second_moment_bound (dyadicIndices (dyadicRatio j * X))
      (fun _ => 2 / (dyadicRatio j * X))
      (fun n => backwardWindowAverage (H + 1) (z X) n - primeCenter (z X) (dyadicRatio j * X))
      (fun _ _ => by positivity) 2 (2 * C) (by norm_num) (dyadic_weight_mass _) hh
  have hBl (j : ℕ) : Tendsto (fun H => limsup (band j H) atTop) atTop (𝓝 0) :=
    dyadic_short_interval_limit hM z L V hL hV hz hcoeff hmass
      (dyadicRatio j) (dyadicRatio_pos j) (dyadicRatio_le_one j)
  have hcover (H J : ℕ) : limsup (F H) atTop ≤
      (∑ j ∈ range J, limsup (band j H) atTop) + sqrt (dyadicRatio J * C) := by
    apply finite_band_limsup_bound (range J) (F H) (fun j => band j H)
      (fun X => ∑ j ∈ range J,
        2 * (primeCenter (z X) X - primeCenter (z X) (dyadicRatio j * X)) ^ 2)
      (sqrt (dyadicRatio J * C)) (hFn H) (fun j _ => hBb j H)
    · convert! tendsto_finsetSum (range J) (fun j _ =>
        ((primeCenter_fixed_ratio_tendsto_zero z L (dyadicRatio j)
          (dyadicRatio_pos j) (dyadicRatio_le_one j) hcoeff).pow 2).const_mul 2) using 1
      simp
    · filter_upwards [h4 H, eventually_gt_atTop (0 : ℝ)] with X hh hX
      exact shortInterval_dyadic_cover H J (z X) X C hX hh
  have htail : Tendsto (fun J => sqrt (dyadicRatio J * C)) atTop (𝓝 0) := by
    have hr : Tendsto dyadicRatio atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using (hr.mul_const C).sqrt
  change Tendsto (fun H => limsup (F H) atTop) atTop (𝓝 0)
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall fun H => hr.trans_le (limsup_nonneg (hFn H) (hFb H))
  · intro ε hε
    obtain ⟨J, hJ⟩ := (htail.eventually (eventually_lt_nhds (show 0 < ε / 2 by positivity))).exists
    have hs : Tendsto (fun H => ∑ j ∈ range J, limsup (band j H) atTop) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (range J) (fun j _ => hBl j)
    filter_upwards [hs.eventually (eventually_lt_nhds (show 0 < ε / 2 by positivity))] with H hH
    linarith [hcover H J]

/-- Lemma 2.1 in the manuscript's normalization and order of limits. -/
theorem lemma_2_1 (hM : Mangerel)
    (z : ℝ → ℕ → ℝ) (L V : ℝ) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hz : ∀ X, IsStronglyAdditive (z X))
    (hcoeff : ∀ X p, p.Prime → |z X p| ≤ L)
    (hmass : ∀ X, 2 ≤ X → primeMoment (z X) X 2 ≤ V) :
    Tendsto (fun H : ℕ => limsup (fun X : ℝ =>
      (∑ n ∈ Icc H ⌊X⌋₊,
        (backwardWindowAverage H (z X) n - primeCenter (z X) X) ^ 2) / X) atTop)
      atTop (𝓝 0) := by
  have he (H : ℕ) (X : ℝ) : shortIntervalMoment H (z X) X 2 =
      (∑ n ∈ Icc H ⌊X⌋₊,
        (backwardWindowAverage H (z X) n - primeCenter (z X) X) ^ 2) / X := by
    unfold shortIntervalMoment
    rw [← mul_sum]
    ring
  simpa only [he] using short_interval_second_moment hM z L V hL hV hz hcoeff hmass

end

end Erdos1122
