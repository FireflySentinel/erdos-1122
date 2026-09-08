import Erdos1122.PrimePowerCenter

/-! # Moment contraction on the manuscript's backward windows -/

namespace Erdos1122

open Finset Real

noncomputable section

theorem backwardWindowAverage_sub_const (H : ℕ) (hH : 0 < H) (f : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    backwardWindowAverage H (fun m => f m - c) n = backwardWindowAverage H f n - c := by
  unfold backwardWindowAverage
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hh : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

theorem backward_shifted_sum_le (S : Finset ℕ) (H N j : ℕ) (hj : j < H)
    (hS : ∀ n ∈ S, H ≤ n ∧ n ≤ N) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ S, g (n - j)) ≤ ∑ m ∈ Ioc 0 N, g m := by
  classical
  have hi : Set.InjOn (fun n : ℕ => n - j) S := by
    intro n hn m hm he
    have := hS n hn
    have := hS m hm
    dsimp at he
    omega
  calc
    _ = ∑ m ∈ S.image (fun n => n - j), g m := (sum_image hi).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := mem_image.1 hm
        have := hS n hn
        simp only [mem_Ioc]
        omega
      · intro m _ _
        exact hg m

theorem backward_fourth_contraction (S : Finset ℕ) (H N : ℕ) (hH : 0 < H)
    (hS : ∀ n ∈ S, H ≤ n ∧ n ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ S, (backwardWindowAverage H f n) ^ 4) ≤ ∑ m ∈ Ioc 0 N, f m ^ 4 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ ∑ n ∈ S, (∑ j ∈ range H, f (n - j) ^ 4) / (H : ℝ) := by
      apply sum_le_sum
      intro n _
      simpa [backwardWindowAverage] using
        finite_mean_fourth_le (range H) (fun j => f (n - j)) (by simpa using hH)
    _ = (∑ j ∈ range H, ∑ n ∈ S, f (n - j) ^ 4) / (H : ℝ) := by
      rw [← sum_div, sum_comm]
    _ ≤ (∑ _j ∈ range H, ∑ m ∈ Ioc 0 N, f m ^ 4) / (H : ℝ) := by
      apply div_le_div_of_nonneg_right _ hHr.le
      exact sum_le_sum fun j hj => backward_shifted_sum_le S H N j (mem_range.1 hj) hS
        (fun n => f n ^ 4) (fun _ => by positivity)
    _ = _ := by simp [hHr.ne']

theorem backward_second_contraction (S : Finset ℕ) (H N : ℕ) (hH : 0 < H)
    (hS : ∀ n ∈ S, H ≤ n ∧ n ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ S, (backwardWindowAverage H f n) ^ 2) ≤ ∑ m ∈ Ioc 0 N, f m ^ 2 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ ∑ n ∈ S, (∑ j ∈ range H, f (n - j) ^ 2) / (H : ℝ) := by
      apply sum_le_sum
      intro n _
      simpa [backwardWindowAverage] using
        finite_mean_square_le (range H) (fun j => f (n - j)) (by simpa using hH)
    _ = (∑ j ∈ range H, ∑ n ∈ S, f (n - j) ^ 2) / (H : ℝ) := by
      rw [← sum_div, sum_comm]
    _ ≤ (∑ _j ∈ range H, ∑ m ∈ Ioc 0 N, f m ^ 2) / (H : ℝ) := by
      apply div_le_div_of_nonneg_right _ hHr.le
      exact sum_le_sum fun j hj => backward_shifted_sum_le S H N j (mem_range.1 hj) hS
        (fun n => f n ^ 2) (fun _ => by positivity)
    _ = _ := by simp [hHr.ne']

end

end Erdos1122
