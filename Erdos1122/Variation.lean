import Erdos1122.Averaging

/-!
# Total variation and short windows

This gives a finite, quantitative version of the bounded-observable argument
in Section 6. In particular, the bound is uniform over changing functions.
-/

namespace Erdos1122

open Finset

noncomputable section

def totalVariation (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, |f (n + 1) - f n|

theorem totalVariation_nonneg (f : ℕ → ℝ) (N : ℕ) : 0 ≤ totalVariation f N :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem displacement_le_variation (f : ℕ → ℝ) (n j : ℕ) :
    |f (n + j) - f n| ≤ ∑ k ∈ range j, |f (n + k + 1) - f (n + k)| := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [sum_range_succ]
      have h := abs_sub_le (f (n + j + 1)) (f (n + j)) (f n)
      change |f (n + j + 1) - f n| ≤ _
      linarith

theorem summed_displacement_le (f : ℕ → ℝ) (N H j : ℕ) (hj : j < H) :
    (∑ n ∈ range N, |f n - f (n + j)|)
      ≤ (H : ℝ) * totalVariation f (N + H) := by
  calc
    _ ≤ ∑ n ∈ range N, ∑ k ∈ range j, |f (n + k + 1) - f (n + k)| := by
      apply sum_le_sum
      intro n _hn
      rw [abs_sub_comm]
      exact displacement_le_variation f n j
    _ = ∑ k ∈ range j, ∑ n ∈ range N, |f (n + k + 1) - f (n + k)| :=
      sum_comm
    _ ≤ ∑ _k ∈ range j, totalVariation f (N + H) := by
      apply sum_le_sum
      intro k hk
      exact shifted_sum_le (fun m => |f (m + 1) - f m|)
        (fun _ => abs_nonneg _) N H k (by have := mem_range.mp hk; omega)
    _ = (j : ℝ) * totalVariation f (N + H) := by simp
    _ ≤ (H : ℝ) * totalVariation f (N + H) := by
      apply mul_le_mul_of_nonneg_right _ (totalVariation_nonneg f _)
      exact_mod_cast hj.le

theorem abs_window_discrepancy_le (f : ℕ → ℝ) (H n : ℕ) (hH : 0 < H) :
    |f n - windowAverage H f n|
      ≤ (∑ j ∈ range H, |f n - f (n + j)|) / (H : ℝ) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have he : f n - windowAverage H f n =
      (∑ j ∈ range H, (f n - f (n + j))) / (H : ℝ) := by
    simp only [windowAverage, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [he, abs_div, abs_of_pos hHr]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hHr.le

theorem sum_abs_window_discrepancy_le (f : ℕ → ℝ) (N H : ℕ) (hH : 0 < H) :
    (∑ n ∈ range N, |f n - windowAverage H f n|)
      ≤ (H : ℝ) * totalVariation f (N + H) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ ∑ n ∈ range N, (∑ j ∈ range H, |f n - f (n + j)|) / (H : ℝ) :=
      sum_le_sum fun n _hn => abs_window_discrepancy_le f H n hH
    _ = (∑ j ∈ range H, ∑ n ∈ range N, |f n - f (n + j)|) / (H : ℝ) := by
      rw [← sum_div, sum_comm]
    _ ≤ (∑ _j ∈ range H, (H : ℝ) * totalVariation f (N + H)) / (H : ℝ) := by
      apply div_le_div_of_nonneg_right _ hHr.le
      exact sum_le_sum fun j hj => summed_displacement_le f N H j (mem_range.mp hj)
    _ = (H : ℝ) * totalVariation f (N + H) := by simp [hHr.ne']

theorem abs_windowAverage_le (f : ℕ → ℝ) (N H n : ℕ) (hH : 0 < H)
    (hn : n < N) (K : ℝ) (hb : ∀ m < N + H, |f m| ≤ K) :
    |windowAverage H f n| ≤ K := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  rw [windowAverage, abs_div, abs_of_pos hHr]
  apply (div_le_iff₀ hHr).mpr
  calc
    |∑ j ∈ range H, f (n + j)| ≤ ∑ j ∈ range H, |f (n + j)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range H, K := by
      apply sum_le_sum
      intro j hj
      apply hb
      have := mem_range.mp hj
      omega
    _ = K * (H : ℝ) := by simp [mul_comm]

/-- The finite estimate that turns `o(N)` variation into vanishing mean-square
discrepancy on each fixed window length. -/
theorem sum_square_window_discrepancy_le (f : ℕ → ℝ) (N H : ℕ) (hH : 0 < H)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ m < N + H, |f m| ≤ K) :
    (∑ n ∈ range N, (f n - windowAverage H f n) ^ 2)
      ≤ 2 * K * (H : ℝ) * totalVariation f (N + H) := by
  calc
    _ ≤ ∑ n ∈ range N, 2 * K * |f n - windowAverage H f n| := by
      apply sum_le_sum
      intro n hn
      have hnN := mem_range.mp hn
      have hfn := hb n (by omega)
      have hwin := abs_windowAverage_le f N H n hH hnN K hb
      have habs : |f n - windowAverage H f n| ≤ 2 * K := by
        have htri := abs_sub (f n) (windowAverage H f n)
        linarith
      have hm := mul_le_mul_of_nonneg_right habs
        (abs_nonneg (f n - windowAverage H f n))
      nlinarith [sq_abs (f n - windowAverage H f n)]
    _ = 2 * K * ∑ n ∈ range N, |f n - windowAverage H f n| := by rw [mul_sum]
    _ ≤ 2 * K * ((H : ℝ) * totalVariation f (N + H)) := by
      exact mul_le_mul_of_nonneg_left (sum_abs_window_discrepancy_le f N H hH)
        (by positivity)
    _ = 2 * K * (H : ℝ) * totalVariation f (N + H) := by ring

end

end Erdos1122
