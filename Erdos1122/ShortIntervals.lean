import Erdos1122.Interpolation
import Erdos1122.Limits

/-!
# Uniform first-to-second moment transfer

The first-moment estimate and fourth-moment bound are hypotheses. The finite
sets, weights, and function values may all vary with the large parameter `X`.
In particular, the function is not fixed before `X` tends to infinity.
-/

namespace Erdos1122

open Finset Filter Topology

noncomputable section

variable {ι α : Type*} [Preorder α] [NeBot (atTop : Filter α)]

theorem weighted_second_moment_bound (t : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (W C : ℝ) (hW : 0 ≤ W)
    (hmass : ∑ i ∈ t, w i ≤ W) (hfourth : ∑ i ∈ t, w i * f i ^ 4 ≤ C) :
    ∑ i ∈ t, w i * f i ^ 2 ≤ W * C + 1 := by
  have hcauchy : (∑ i ∈ t, w i * f i ^ 2) ^ 2 ≤
      (∑ i ∈ t, w i) * ∑ i ∈ t, w i * f i ^ 4 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul t hw
      (fun i hi => mul_nonneg (hw i hi) (by positivity))
    intro i _
    exact le_of_eq (by ring)
  have h4 : 0 ≤ ∑ i ∈ t, w i * f i ^ 4 :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (by positivity)
  have hp := mul_le_mul hmass hfourth h4 hW
  nlinarith [sq_nonneg ((∑ i ∈ t, w i * f i ^ 2) - 1)]

/-- The omitted initial segment is controlled by its mass and the full fourth moment. -/
theorem restricted_second_moment_bound (s t : Finset ι) (w f : ι → ℝ)
    (hst : s ⊆ t) (hw : ∀ i ∈ t, 0 ≤ w i) (η C : ℝ) (hη : 0 ≤ η)
    (hmass : ∑ i ∈ s, w i ≤ η) (hfourth : ∑ i ∈ t, w i * f i ^ 4 ≤ C) :
    ∑ i ∈ s, w i * f i ^ 2 ≤ Real.sqrt (η * C) := by
  have hcauchy : (∑ i ∈ s, w i * f i ^ 2) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * f i ^ 4 := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i hi => hw i (hst hi))
      (fun i hi => mul_nonneg (hw i (hst hi)) (by positivity))
    intro i _
    exact le_of_eq (by ring)
  have h4 : (∑ i ∈ s, w i * f i ^ 4) ≤ C := by
    apply le_trans _ hfourth
    exact sum_le_sum_of_subset_of_nonneg hst (fun i hi _ => mul_nonneg (hw i hi) (by positivity))
  have h4n : 0 ≤ ∑ i ∈ s, w i * f i ^ 4 :=
    sum_nonneg fun i hi => mul_nonneg (hw i (hst hi)) (by positivity)
  exact Real.le_sqrt_of_sq_le (hcauchy.trans (mul_le_mul hmass h4 h4n hη))

/-- The uniform analytic transfer used on a fixed dyadic band in Lemma 2.1.
`hfirst` is the shape supplied by Mangerel's estimate: one error depends on
`H`, another on `X`; both tend to zero. Its constant is fixed for the family.
`hfourth` is the uniform fourth-moment bound. -/
theorem uniform_first_fourth_moment_transfer
    (t : α → Finset ι) (w : α → ι → ℝ) (F : ℕ → α → ι → ℝ)
    (W C : ℝ) (hW : 0 ≤ W)
    (hw : ∀ X i, i ∈ t X → 0 ≤ w X i)
    (hmass : ∀ X, ∑ i ∈ t X, w X i ≤ W)
    (hfourth : ∀ H, ∀ᶠ X in atTop, ∑ i ∈ t X, w X i * F H X i ^ 4 ≤ C)
    (a : ℕ → ℝ) (b : α → ℝ) (H₀ : ℕ)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hfirst : ∀ H, H₀ ≤ H → ∀ᶠ X in atTop,
      ∑ i ∈ t X, w X i * |F H X i| ≤ a H + b X) :
    Tendsto (fun H => limsup (fun X => ∑ i ∈ t X, w X i * F H X i ^ 2) atTop)
      atTop (𝓝 0) := by
  let S₂ := fun H X => ∑ i ∈ t X, w X i * F H X i ^ 2
  have hn (H : ℕ) (X : α) : 0 ≤ S₂ H X :=
    sum_nonneg fun i hi => mul_nonneg (hw X i hi) (sq_nonneg _)
  have hbounded (H : ℕ) : IsBoundedUnder (· ≤ ·) atTop (S₂ H) := by
    refine ⟨W * C + 1, ?_⟩
    change ∀ᶠ X in atTop, S₂ H X ≤ W * C + 1
    filter_upwards [hfourth H] with X hX
    exact weighted_second_moment_bound (t X) (w X) (F H X) (hw X) W C hW (hmass X) hX
  change Tendsto (fun H => limsup (S₂ H) atTop) atTop (𝓝 0)
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall fun H => hr.trans_le (limsup_nonneg (hn H) (hbounded H))
  · intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hpoly : Tendsto (fun δ : ℝ => δ ^ 2 * C) (𝓝[>] 0) (𝓝 0) := by
      convert! ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2).mul_const C using 1
      simp
    obtain ⟨δ, hδ, hδsmall⟩ :=
      ((show ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ from self_mem_nhdsWithin).and
        (hpoly.eventually (eventually_lt_nhds (pow_pos hhalf 3)))).exists
    have hδhalf : 0 < δ / 2 := by positivity
    filter_upwards [eventually_ge_atTop H₀,
      ha.eventually (eventually_lt_nhds hδhalf)] with H hH haH
    have hevent : ∀ᶠ X in atTop, S₂ H X ≤ ε / 2 := by
      filter_upwards [hfourth H, hfirst H hH,
        hb.eventually (eventually_lt_nhds hδhalf)] with X h4 h1 hbX
      have h1n : 0 ≤ ∑ i ∈ t X, w X i * |F H X i| :=
        sum_nonneg fun i hi => mul_nonneg (hw X i hi) (abs_nonneg _)
      have h1δ : (∑ i ∈ t X, w X i * |F H X i|) ^ 2 ≤ δ ^ 2 := by nlinarith
      have hinterp := weighted_moment_interpolation (t X) (w X) (F H X) (hw X)
      have h4n : 0 ≤ ∑ i ∈ t X, w X i * F H X i ^ 4 :=
        sum_nonneg fun i hi => mul_nonneg (hw X i hi) (by positivity)
      have hp := mul_le_mul h1δ h4 h4n (sq_nonneg δ)
      have hcube : S₂ H X ^ 3 < (ε / 2) ^ 3 := lt_of_le_of_lt (hinterp.trans hp) hδsmall
      exact ((pow_le_pow_iff_left₀ (hn H X) hhalf.le (by decide : 3 ≠ 0)).1 hcube.le)
    exact (limsup_le_of_le (isCoboundedUnder_le_of_le atTop (hn H)) hevent).trans_lt
      (by linarith)

/-- Passing from finitely many bands to their union, with a vanishing center or
endpoint error. The number of bands is fixed before taking the `X` limit. -/
theorem finite_band_limsup_bound (s : Finset ι) (F : α → ℝ)
    (band : ι → α → ℝ) (error : α → ℝ) (tail : ℝ)
    (hF : ∀ X, 0 ≤ F X)
    (hband : ∀ i ∈ s, IsBoundedUnder (· ≤ ·) atTop (band i))
    (herror : Tendsto error atTop (𝓝 0))
    (hcover : ∀ᶠ X in atTop, F X ≤ (∑ i ∈ s, band i X) + error X + tail) :
    limsup F atTop ≤ (∑ i ∈ s, limsup (band i) atTop) + tail := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / ((s.card : ℝ) + 1)
  have hc : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hc
  have hall : ∀ᶠ X in atTop, ∀ i ∈ s, band i X < limsup (band i) atTop + δ := by
    apply (eventually_all_finset s).2
    intro i hi
    exact eventually_lt_of_limsup_lt (by linarith) (hband i hi)
  have hcancel : (s.card : ℝ) * δ + δ = ε := by dsimp [δ]; field_simp
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop hF)
  filter_upwards [hcover, hall, herror.eventually (eventually_lt_nhds hδ)] with X hc hb he
  have hsum := sum_le_sum (fun i hi => (hb i hi).le)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
  linarith

/-- Full-interval assembly from fixed finite bands. The band estimates can be
obtained by `uniform_first_fourth_moment_transfer`; the cover and center error
are separate, explicit hypotheses. -/
theorem full_interval_from_finite_bands
    (F : ℕ → α → ℝ) (band : ℕ → ℕ → α → ℝ)
    (s : ℝ → Finset ℕ) (error : ℝ → ℕ → α → ℝ) (tail : ℝ → ℝ)
    (hF : ∀ H X, 0 ≤ F H X)
    (hbounded : ∀ H, IsBoundedUnder (· ≤ ·) atTop (F H))
    (hbandBounded : ∀ j H, IsBoundedUnder (· ≤ ·) atTop (band j H))
    (hband : ∀ j, Tendsto (fun H => limsup (band j H) atTop) atTop (𝓝 0))
    (herror : ∀ η, 0 < η → ∀ H, Tendsto (error η H) atTop (𝓝 0))
    (htail : Tendsto tail (𝓝[>] 0) (𝓝 0))
    (hcover : ∀ η, 0 < η → ∀ H, ∀ᶠ X in atTop,
      F H X ≤ (∑ j ∈ s η, band j H X) + error η H X + tail η) :
    Tendsto (fun H => limsup (F H) atTop) atTop (𝓝 0) := by
  apply iterated_limsup_zero F
    (fun η H => ∑ j ∈ s η, limsup (band j H) atTop) tail hF hbounded _ htail
  · intro η hη
    exact Eventually.of_forall fun H => finite_band_limsup_bound (s η) (F H)
      (fun j => band j H) (error η H) (tail η) (hF H)
      (fun j _ => hbandBounded j H) (herror η hη H) (hcover η hη H)
  · intro η _
    simpa using tendsto_finsetSum (s η) (fun j _ => hband j)

end

end Erdos1122
