import Erdos1122.Minimizer
import Mathlib.Topology.Order.IntermediateValue

/-! # The scale parameter in Lemma 4.1

All minimizers lie in one compact interval, independent of the positive scale.
This makes continuity of the minimum an application of the compact minimum
theorem. Attainment of a prescribed mass requires an explicit lower value at
some scale; that hypothesis cannot be omitted for an arbitrary finite array.
-/

namespace Erdos1122

open Finset Filter Topology

noncomputable section

variable {ι : Type*}

def scaleRadius (t : Finset ι) (w : ι → ℝ) : ℝ := 1 + ∑ i ∈ t, w i

def scaledMinimum (t : Finset ι) (w a l : ι → ℝ) (s : ℝ) : ℝ :=
  sInf (cappedQuadratic t w (fun i => a i / s) l ''
    Set.Icc (-scaleRadius t w) (scaleRadius t w))

private theorem minimizer_in_interval (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (c : ℝ)
    (hc : ∀ x, cappedQuadratic t w a l c ≤ cappedQuadratic t w a l x) :
    c ∈ Set.Icc (-scaleRadius t w) (scaleRadius t w) := by
  have hW : 0 ≤ ∑ i ∈ t, w i := sum_nonneg hw
  have h0 : cappedQuadratic t w a l 0 ≤ ∑ i ∈ t, w i := by
    simp only [cappedQuadratic, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, zero_add]
    exact sum_le_sum fun i hi => mul_le_of_le_one_right (hw i hi) (min_le_right _ _)
  have hsq := (sq_le_cappedQuadratic t w a l hw c).trans ((hc 0).trans h0)
  dsimp [scaleRadius]
  constructor <;> nlinarith [sq_nonneg (c + 1), sq_nonneg (c - 1)]

theorem scaledMinimum_attained (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (s : ℝ) :
    ∃ c, scaledMinimum t w a l s = cappedQuadratic t w (fun i => a i / s) l c ∧
      ∀ x, cappedQuadratic t w (fun i => a i / s) l c ≤
        cappedQuadratic t w (fun i => a i / s) l x := by
  obtain ⟨c, hc⟩ := cappedQuadratic_exists_min t w (fun i => a i / s) l hw
  refine ⟨c, ?_, hc⟩
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨_, Set.mem_image_of_mem _ (minimizer_in_interval t w _ l hw c hc)⟩
  · rintro y ⟨x, _, rfl⟩
    exact hc x
  · intro b hb
    exact ⟨_, Set.mem_image_of_mem _ (minimizer_in_interval t w _ l hw c hc), hb⟩

theorem scaledMinimum_nonneg (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (s : ℝ) : 0 ≤ scaledMinimum t w a l s := by
  obtain ⟨c, hc, _⟩ := scaledMinimum_attained t w a l hw s
  rw [hc]
  exact (sq_nonneg c).trans (sq_le_cappedQuadratic t w _ l hw c)

theorem scaledMinimum_le (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (s c : ℝ) :
    scaledMinimum t w a l s ≤ cappedQuadratic t w (fun i => a i / s) l c := by
  obtain ⟨x, hx, hmin⟩ := scaledMinimum_attained t w a l hw s
  rw [hx]
  exact hmin c

theorem scaledMinimum_continuousOn (t : Finset ι) (w a l : ι → ℝ) :
    ContinuousOn (scaledMinimum t w a l) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply isCompact_Icc.continuous_sInf
  change Continuous (fun q : {s : ℝ // s ∈ Set.Ioi 0} × ℝ =>
    cappedQuadratic t w (fun i => a i / q.1.val) l q.2)
  unfold cappedQuadratic
  have hn (q : {s : ℝ // s ∈ Set.Ioi 0} × ℝ) : q.1.val ≠ 0 := ne_of_gt q.1.property
  fun_prop

private theorem capped_scale_le (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (s r c : ℝ) (hs : 0 < s) (hsr : s ≤ r) :
    cappedQuadratic t w (fun i => a i / r) l ((s / r) * c) ≤
      cappedQuadratic t w (fun i => a i / s) l c := by
  have hr : 0 < r := hs.trans_le hsr
  have hk : 0 ≤ s / r := div_nonneg hs.le hr.le
  have hk1 : s / r ≤ 1 := (div_le_one hr).2 hsr
  have hsq (x : ℝ) : ((s / r) * x) ^ 2 ≤ x ^ 2 := by
    have hh : (s / r) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg x)]
  apply add_le_add (hsq c)
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  have he : a i / r - s / r * c * l i = (s / r) * (a i / s - c * l i) := by
    field_simp
  rw [he]
  exact min_le_min_right 1 (hsq _)

theorem scaledMinimum_antitoneOn (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) : AntitoneOn (scaledMinimum t w a l) (Set.Ioi 0) := by
  intro s hs r _ hsr
  obtain ⟨c, hc, _⟩ := scaledMinimum_attained t w a l hw s
  rw [hc]
  exact (scaledMinimum_le t w a l hw r ((s / r) * c)).trans
    (capped_scale_le t w a l hw s r c hs hsr)

theorem scaledMinimum_tendsto_zero (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) :
    Tendsto (scaledMinimum t w a l) atTop (𝓝 0) := by
  have hb (s : ℝ) : scaledMinimum t w a l s ≤ ∑ i ∈ t, w i * (a i / s) ^ 2 := by
    apply (scaledMinimum_le t w a l hw s 0).trans
    simp only [cappedQuadratic, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, zero_add]
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (min_le_left _ _) (hw i hi)
  have hz : Tendsto (fun s : ℝ => ∑ i ∈ t, w i * (a i / s) ^ 2) atTop (𝓝 0) := by
    have hi (i : ι) : Tendsto (fun s : ℝ => w i * (a i / s) ^ 2) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul tendsto_inv_atTop_zero).pow 2) :
          Tendsto (fun s : ℝ => w i * (a i * s⁻¹) ^ 2) atTop (𝓝 (w i * (a i * 0) ^ 2)))
    simpa using tendsto_finsetSum t (fun i _ => hi i)
  exact squeeze_zero (scaledMinimum_nonneg t w a l hw) hb hz

/-- The intermediate-value step. For a fixed finite array, a mass below the
value at `s₀` is attained at a larger scale. -/
theorem scaledMinimum_exists_scale (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (s₀ M : ℝ) (hs₀ : 0 < s₀) (hM : 0 < M)
    (hstart : M < scaledMinimum t w a l s₀) :
    ∃ s : ℝ, s₀ < s ∧ scaledMinimum t w a l s = M := by
  have hev := (scaledMinimum_tendsto_zero t w a l hw).eventually (gt_mem_nhds hM)
  obtain ⟨r, hval⟩ := (eventually_atTop.1 hev)
  let s₁ := max r (s₀ + 1)
  have h₁ : s₀ ≤ s₁ := by dsimp [s₁]; linarith [le_max_right r (s₀ + 1)]
  have hsmall : scaledMinimum t w a l s₁ < M := hval s₁ (le_max_left _ _)
  have hcont := (scaledMinimum_continuousOn t w a l).mono
    (show Set.Icc s₀ s₁ ⊆ Set.Ioi 0 from fun s hs => hs₀.trans_le hs.1)
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' h₁ hcont ⟨hsmall.le, hstart.le⟩
  refine ⟨s, lt_of_le_of_ne hs.1 ?_, he⟩
  intro heq
  subst s
  linarith

/-- Once the fixed-scale divergence has been supplied, any positive choices
at the prescribed level tend to infinity. The scale is chosen after `X`;
there is no uniform convergence assumption in the scale parameter. -/
theorem scales_tendsto_atTop_of_level (W : ℝ → ℝ → ℝ) (s : ℝ → ℝ) (M : ℝ)
    (hmono : ∀ X, AntitoneOn (W X) (Set.Ioi 0))
    (hdiv : ∀ r : ℝ, 0 < r → Tendsto (fun X => W X r) atTop atTop)
    (hlevel : ∀ᶠ X in atTop, 0 < s X ∧ W X (s X) = M) :
    Tendsto s atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let r := max b 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right b 1]
  filter_upwards [(hdiv r hr).eventually (eventually_gt_atTop M), hlevel] with X hX hs
  by_contra hb
  have hsr : s X ≤ r := (le_of_not_ge hb).trans (le_max_left _ _)
  have h := hmono X hs.1 hr hsr
  rw [hs.2] at h
  linarith

end

end Erdos1122
