import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Clipping estimates

The scalar and finite-sum estimates used in Section 5 of `paper/PROOF.tex`.
The arguments concern arbitrary real inputs and finite sets, not a numerical
sample of prime values.
-/

namespace Erdos1122

open Finset

noncomputable section

/-- Clipping to `[-K, K]`, with the parameter supplied explicitly. -/
def clip (K x : ℝ) : ℝ := max (-K) (min x K)

theorem neg_le_clip (K x : ℝ) : -K ≤ clip K x := le_max_left _ _

theorem clip_le (hK : 0 ≤ K) (x : ℝ) : clip K x ≤ K :=
  max_le (by linarith) (min_le_right _ _)

theorem abs_clip_le (hK : 0 ≤ K) (x : ℝ) : |clip K x| ≤ K :=
  abs_le.mpr ⟨neg_le_clip K x, clip_le hK x⟩

theorem clip_eq_self (hx : |x| ≤ K) : clip K x = x := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  simp only [clip, min_eq_left hu, max_eq_right hl]

theorem clip_monotone (K : ℝ) : Monotone (clip K) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min hxy le_rfl)

theorem clip_lipschitz (K x y : ℝ) : |clip K x - clip K y| ≤ |x - y| := by
  calc
    |clip K x - clip K y|
        ≤ max |(-K) - (-K)| |min x K - min y K| :=
      abs_max_sub_max_le_max _ _ _ _
    _ = |min x K - min y K| := by simp
    _ ≤ max |x - y| |K - K| := abs_min_sub_min_le_max _ _ _ _
    _ = |x - y| := by simp

theorem abs_clip_eq_min (hK : 0 ≤ K) (x : ℝ) :
    |clip K x| = min |x| K := by
  rcases le_total x (-K) with hlow | hlow
  · have hxK : x ≤ K := by linarith
    have hx0 : x ≤ 0 := by linarith
    have hbound : K ≤ -x := by linarith
    simp [clip, min_eq_left hxK, max_eq_left hlow, abs_of_nonpos hx0,
      abs_of_nonneg hK, min_eq_right hbound]
  · by_cases hhigh : x ≤ K
    · have hx : |x| ≤ K := abs_le.mpr ⟨hlow, hhigh⟩
      rw [clip_eq_self hx, min_eq_left hx]
    · have hxK : K ≤ x := le_of_lt (lt_of_not_ge hhigh)
      have hx0 : 0 ≤ x := le_trans hK hxK
      simp [clip, min_eq_right hxK, max_eq_right (show -K ≤ K by linarith),
        abs_of_nonneg hK, abs_of_nonneg hx0]

theorem abs_clip_residual (hK : 0 ≤ K) (x : ℝ) :
    |clip K x - x| = max (|x| - K) 0 := by
  rcases le_total x (-K) with hlow | hlow
  · have hxK : x ≤ K := by linarith
    have hx0 : x ≤ 0 := by linarith
    have he : 0 ≤ -K - x := by linarith
    have hr : 0 ≤ -x - K := by linarith
    simp only [clip, min_eq_left hxK, max_eq_left hlow, abs_of_nonneg he,
      abs_of_nonpos hx0, max_eq_left hr]
    ring
  · by_cases hhigh : x ≤ K
    · have hx : |x| ≤ K := abs_le.mpr ⟨hlow, hhigh⟩
      rw [clip_eq_self hx, sub_self, abs_zero, max_eq_right (sub_nonpos.mpr hx)]
    · have hxK : K ≤ x := le_of_lt (lt_of_not_ge hhigh)
      have hx0 : 0 ≤ x := le_trans hK hxK
      simp only [clip, min_eq_right hxK,
        max_eq_right (show -K ≤ K by linarith),
        abs_of_nonpos (sub_nonpos.mpr hxK), abs_of_nonneg hx0,
        max_eq_left (sub_nonneg.mpr hxK)]
      ring

/-- The one-tail-prime estimate in the clipping argument. -/
theorem clip_single_tail_error (K s v : ℝ) :
    |clip K (s + v) - s - clip K v| ≤ 2 * |s| := by
  have hl := clip_lipschitz K (s + v) v
  simp only [add_sub_cancel_right] at hl
  calc
    |clip K (s + v) - s - clip K v|
        = |(clip K (s + v) - clip K v) + (-s)| := by congr 1; ring
    _ ≤ |clip K (s + v) - clip K v| + |-s| := abs_add_le _ _
    _ ≤ 2 * |s| := by rw [abs_neg]; linarith

/-- The no-tail error is controlled by the fourth moment. -/
theorem clip_no_tail_error_sq (hK : 0 < K) (s : ℝ) :
    (clip K s - s) ^ 2 ≤ s ^ 4 / K ^ 2 := by
  by_cases hs : |s| ≤ K
  · rw [clip_eq_self hs, sub_self, zero_pow (by decide)]
    positivity
  · have hsK : K ≤ |s| := le_of_lt (lt_of_not_ge hs)
    have he : |clip K s - s| ≤ |s| := by
      rw [abs_clip_residual hK.le]
      exact max_le (by linarith) (abs_nonneg s)
    have hesq : (clip K s - s) ^ 2 ≤ s ^ 2 := by
      nlinarith [sq_abs (clip K s - s), sq_abs s, abs_nonneg (clip K s - s),
        abs_nonneg s]
    have hsq : K ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs s]
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg s)
    apply le_trans hesq
    apply (le_div_iff₀ (sq_pos_of_pos hK)).mpr
    nlinarith

/-- Clipping retains truncated quadratic mass, and increases it by at most `K²`. -/
theorem clipped_square_bounds (hK : 1 ≤ K) (x : ℝ) :
    min (x ^ 2) 1 ≤ (clip K x) ^ 2 ∧
      (clip K x) ^ 2 ≤ K ^ 2 * min (x ^ 2) 1 := by
  have hK0 : 0 ≤ K := by linarith
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  by_cases hx : |x| ≤ 1
  · have hxK : |x| ≤ K := le_trans hx hK
    have hxsq : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    rw [clip_eq_self hxK, min_eq_left hxsq]
    constructor
    · exact le_rfl
    · nlinarith [mul_nonneg (sub_nonneg.mpr hKsq) (sq_nonneg x)]
  · have hx1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hxsq : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
    rw [min_eq_right hxsq, mul_one]
    have hlo : 1 ≤ |clip K x| := by
      rw [abs_clip_eq_min hK0]
      exact le_min hx1 hK
    have hhi := abs_clip_le hK0 x
    constructor <;> nlinarith [sq_abs (clip K x), abs_nonneg (clip K x)]

theorem abs_sum_clip_le {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (hK : 0 ≤ K) : |∑ i ∈ t, clip K (u i)| ≤ (t.card : ℝ) * K := by
  calc
    |∑ i ∈ t, clip K (u i)| ≤ ∑ i ∈ t, |clip K (u i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ t, K := sum_le_sum fun i _hi => abs_clip_le hK (u i)
    _ = (t.card : ℝ) * K := by simp

/-- The multiple-tail-prime estimate, with an explicit absolute constant. -/
theorem clip_many_tail_error_sq {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (hK : 0 ≤ K) (ht : 2 ≤ t.card) (s : ℝ) :
    (clip K (s + ∑ i ∈ t, u i) - (s + ∑ i ∈ t, clip K (u i))) ^ 2
      ≤ 2 * s ^ 2 + 9 * K ^ 2 * (t.card : ℝ) * ((t.card : ℝ) - 1) := by
  have hcount : (2 : ℝ) ≤ t.card := by exact_mod_cast ht
  have hb : |clip K (s + ∑ i ∈ t, u i) - (s + ∑ i ∈ t, clip K (u i))|
      ≤ |s| + K * ((t.card : ℝ) + 1) := by
    calc
      _ ≤ |clip K (s + ∑ i ∈ t, u i)| + |s + ∑ i ∈ t, clip K (u i)| :=
        abs_sub _ _
      _ ≤ K + (|s| + |∑ i ∈ t, clip K (u i)|) :=
        add_le_add (abs_clip_le hK _) (abs_add_le _ _)
      _ ≤ K + (|s| + (t.card : ℝ) * K) := by
        gcongr
        exact abs_sum_clip_le t u hK
      _ = |s| + K * ((t.card : ℝ) + 1) := by ring
  have hpoly : 2 * ((t.card : ℝ) + 1) ^ 2
      ≤ 9 * (t.card : ℝ) * ((t.card : ℝ) - 1) := by
    nlinarith [sq_nonneg ((t.card : ℝ) - 2)]
  have hm := mul_le_mul_of_nonneg_left hpoly (sq_nonneg K)
  have hbsq := mul_self_le_mul_self (abs_nonneg _) hb
  nlinarith [sq_abs s,
    sq_abs (clip K (s + ∑ i ∈ t, u i) - (s + ∑ i ∈ t, clip K (u i))),
    sq_nonneg (|s| - K * ((t.card : ℝ) + 1))]

/-- The three clipping cases combined into a single pointwise bound. -/
theorem clip_finite_tail_error_sq {ι : Type*} (t : Finset ι) (u : ι → ℝ)
    (hK : 0 < K) (s : ℝ) :
    (clip K (s + ∑ i ∈ t, u i) - (s + ∑ i ∈ t, clip K (u i))) ^ 2
      ≤ s ^ 4 / K ^ 2 + (if t.Nonempty then 4 * s ^ 2 else 0)
          + 9 * K ^ 2 * (t.card : ℝ) * ((t.card : ℝ) - 1) := by
  classical
  by_cases he : t = ∅
  · subst t
    simpa using clip_no_tail_error_sq hK s
  have htpos : 0 < t.card := card_pos.mpr (nonempty_iff_ne_empty.mpr he)
  have htne : t.Nonempty := card_pos.mp htpos
  rw [if_pos htne]
  by_cases hone : t.card = 1
  · obtain ⟨i, rfl⟩ := card_eq_one.mp hone
    simp only [sum_singleton, card_singleton, Nat.cast_one, sub_self, mul_zero,
      add_zero]
    have h := clip_single_tail_error K s (u i)
    have hsquare := mul_self_le_mul_self (abs_nonneg _) h
    have heq : clip K (s + u i) - (s + clip K (u i)) =
        clip K (s + u i) - s - clip K (u i) := by ring
    rw [heq]
    have hf : 0 ≤ s ^ 4 / K ^ 2 := by positivity
    nlinarith [sq_abs (clip K (s + u i) - s - clip K (u i)), sq_abs s]
  · have htwo : 2 ≤ t.card := by omega
    have h := clip_many_tail_error_sq t u hK.le htwo s
    have hf : 0 ≤ s ^ 4 / K ^ 2 := by positivity
    nlinarith [sq_nonneg s]

theorem weighted_clipped_square_bounds {ι : Type*} (t : Finset ι)
    (w u : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i) (hK : 1 ≤ K) :
    (∑ i ∈ t, w i * min ((u i) ^ 2) 1)
        ≤ ∑ i ∈ t, w i * (clip K (u i)) ^ 2 ∧
    (∑ i ∈ t, w i * (clip K (u i)) ^ 2)
        ≤ K ^ 2 * ∑ i ∈ t, w i * min ((u i) ^ 2) 1 := by
  constructor
  · exact sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (clipped_square_bounds hK (u i)).1 (hw i hi)
  · calc
      _ ≤ ∑ i ∈ t, w i * (K ^ 2 * min ((u i) ^ 2) 1) :=
        sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (clipped_square_bounds hK (u i)).2 (hw i hi)
      _ = K ^ 2 * ∑ i ∈ t, w i * min ((u i) ^ 2) 1 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _hi
        ring

end

end Erdos1122
