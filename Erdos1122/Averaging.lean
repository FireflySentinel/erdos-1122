import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite averaging and variation

The averaging contraction and bounded-variation estimates behind Section 6.
Windows are indexed forwards; reversing the indexing gives the backward
windows used in the paper.
-/

namespace Erdos1122

open Finset

noncomputable section

theorem square_sum_le_card_sum_square {ι : Type*} (t : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ t, f i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (f i) ^ 2 := by
  simpa [mul_comm] using sum_mul_sq_le_sq_mul_sq t f (fun _ => (1 : ℝ))

theorem finite_mean_square_le {ι : Type*} (t : Finset ι) (f : ι → ℝ)
    (ht : 0 < t.card) :
    ((∑ i ∈ t, f i) / (t.card : ℝ)) ^ 2
      ≤ (∑ i ∈ t, (f i) ^ 2) / (t.card : ℝ) := by
  have hc : (0 : ℝ) < t.card := by exact_mod_cast ht
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
  calc
    (∑ i ∈ t, f i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (f i) ^ 2 :=
      square_sum_le_card_sum_square t f
    _ = ((∑ i ∈ t, (f i) ^ 2) / (t.card : ℝ)) * (t.card : ℝ) ^ 2 := by
      field_simp

def windowAverage (H : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ range H, f (n + j)) / (H : ℝ)

theorem shifted_sum_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (N H j : ℕ) (hj : j < H) :
    (∑ n ∈ range N, f (n + j)) ≤ ∑ m ∈ range (N + H), f m := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => n + j) (range N) := by
    intro a _ha b _hb hab
    dsimp at hab
    omega
  have hsub : (range N).image (fun n => n + j) ⊆ range (N + H) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    simp only [mem_range] at hn ⊢
    omega
  calc
    (∑ n ∈ range N, f (n + j))
        = ∑ m ∈ (range N).image (fun n => n + j), f m := by
      rw [sum_image hinj]
    _ ≤ ∑ m ∈ range (N + H), f m :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m _hm _hn => hf m)

theorem shifted_square_sum_le (f : ℕ → ℝ) (N H j : ℕ) (hj : j < H) :
    (∑ n ∈ range N, f (n + j) ^ 2) ≤ ∑ m ∈ range (N + H), f m ^ 2 :=
  shifted_sum_le (fun n => f n ^ 2) (fun _ => sq_nonneg _) N H j hj

/-- Summing over windows introduces no factor equal to the window length. -/
theorem window_average_contraction (f : ℕ → ℝ) (N H : ℕ) (hH : 0 < H) :
    (∑ n ∈ range N, (windowAverage H f n) ^ 2)
      ≤ ∑ m ∈ range (N + H), f m ^ 2 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    (∑ n ∈ range N, (windowAverage H f n) ^ 2)
        ≤ ∑ n ∈ range N, (∑ j ∈ range H, f (n + j) ^ 2) / (H : ℝ) := by
      apply sum_le_sum
      intro n _hn
      simpa [windowAverage] using
        finite_mean_square_le (range H) (fun j => f (n + j)) (by simpa using hH)
    _ = (∑ j ∈ range H, ∑ n ∈ range N, f (n + j) ^ 2) / (H : ℝ) := by
      rw [← sum_div, sum_comm]
    _ ≤ (∑ _j ∈ range H, ∑ m ∈ range (N + H), f m ^ 2) / (H : ℝ) := by
      apply div_le_div_of_nonneg_right _ hHr.le
      apply sum_le_sum
      intro j hj
      exact shifted_square_sum_le f N H j (mem_range.mp hj)
    _ = ∑ m ∈ range (N + H), f m ^ 2 := by
      simp [hHr.ne']

theorem four_term_square_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg ((a + b) - (c + d))]

/-- The pointwise four-term comparison before applying the averaging contraction. -/
theorem average_comparison_square (Z Y AZ AY m : ℝ) :
    (Z - m) ^ 2 ≤ 4 * ((Z - Y) ^ 2 + (Y - AY) ^ 2 +
      (AY - AZ) ^ 2 + (AZ - m) ^ 2) := by
  have h := four_term_square_le (Z - Y) (Y - AY) (AY - AZ) (AZ - m)
  convert h using 1
  ring

theorem abs_increment_identity (a b : ℝ) :
    |b - a| = (b - a) + 2 * max (a - b) 0 := by
  by_cases h : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge h)
    rw [abs_of_nonpos (sub_nonpos.mpr hba), max_eq_left (sub_nonneg.mpr hba)]
    ring

theorem total_variation_identity (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, |f (n + 1) - f n|)
      = f N - f 0 + 2 * ∑ n ∈ range N, max (f n - f (n + 1)) 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, sum_range_succ, ih, abs_increment_identity]
      ring

/-- Endpoint boundedness converts a bound on negative increments into total variation. -/
theorem total_variation_le (f e : ℕ → ℝ) (N : ℕ) (K : ℝ)
    (hfirst : |f 0| ≤ K) (hlast : |f N| ≤ K)
    (hneg : ∀ n < N, max (f n - f (n + 1)) 0 ≤ e n) :
    (∑ n ∈ range N, |f (n + 1) - f n|) ≤ 2 * K + 2 * ∑ n ∈ range N, e n := by
  rw [total_variation_identity]
  have hs : (∑ n ∈ range N, max (f n - f (n + 1)) 0) ≤ ∑ n ∈ range N, e n :=
    sum_le_sum fun n hn => hneg n (mem_range.mp hn)
  have hf := abs_le.mp hfirst
  have hl := abs_le.mp hlast
  linarith

end

end Erdos1122
