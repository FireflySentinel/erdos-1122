import Erdos1122.DyadicShortIntervals

/-! # Finite dyadic covering and the small initial segment -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

def dyadicRatio (j : ℕ) : ℝ := (1 / 2) ^ j

theorem dyadicRatio_pos (j : ℕ) : 0 < dyadicRatio j := by unfold dyadicRatio; positivity

theorem dyadicRatio_le_one (j : ℕ) : dyadicRatio j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem dyadicRatio_succ (j : ℕ) (X : ℝ) :
    dyadicRatio (j + 1) * X = (dyadicRatio j * X) / 2 := by
  unfold dyadicRatio
  rw [pow_succ]
  ring

theorem sum_prefix_le_dyadic_and_prefix (H : ℕ) (Y : ℝ)
    (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Icc H ⌊Y⌋₊, g n) ≤ (∑ n ∈ dyadicIndices Y, g n) +
      ∑ n ∈ Icc H ⌊Y / 2⌋₊, g n := by
  classical
  have hsub : Icc H ⌊Y⌋₊ ⊆ dyadicIndices Y ∪ Icc H ⌊Y / 2⌋₊ := by
    intro n hn
    simp only [mem_Icc] at hn
    simp only [mem_union, dyadicIndices, mem_Ioc, mem_Icc]
    omega
  have hd : Disjoint (dyadicIndices Y) (Icc H ⌊Y / 2⌋₊) := by
    apply disjoint_left.2
    intro n hn hm
    have := mem_Ioc.1 hn
    have := mem_Icc.1 hm
    omega
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hg n)).trans_eq (sum_union hd)

theorem finite_dyadic_cover (H J : ℕ) (X : ℝ) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Icc H ⌊X⌋₊, g n) ≤
      (∑ j ∈ range J, ∑ n ∈ dyadicIndices (dyadicRatio j * X), g n) +
        ∑ n ∈ Icc H ⌊dyadicRatio J * X⌋₊, g n := by
  induction J with
  | zero => simp [dyadicRatio]
  | succ J ih =>
      have hh := sum_prefix_le_dyadic_and_prefix H (dyadicRatio J * X) g hg
      rw [sum_range_succ, dyadicRatio_succ]
      linarith

theorem prefix_weight_mass (H : ℕ) (X δ : ℝ) (hX : 0 < X) (hδ : 0 ≤ δ) :
    (∑ _n ∈ Icc (H + 1) ⌊δ * X⌋₊, (1 : ℝ) / X) ≤ δ := by
  have hcard : ((Icc (H + 1) ⌊δ * X⌋₊).card : ℝ) ≤ δ * X := by
    apply le_trans _ (Nat.floor_le (by positivity))
    simp only [Nat.card_Icc]
    exact_mod_cast (show ⌊δ * X⌋₊ + 1 - (H + 1) ≤ ⌊δ * X⌋₊ by omega)
  simp only [sum_const, nsmul_eq_mul]
  simpa [div_eq_mul_inv] using (div_le_iff₀ hX).2 hcard

def shortIntervalMoment (H : ℕ) (f : ℕ → ℝ) (X : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Icc H ⌊X⌋₊, (1 / X) *
    (backwardWindowAverage H f n - primeCenter f X) ^ k

theorem shortIntervalMoment_nonneg (H : ℕ) (f : ℕ → ℝ) (X : ℝ) :
    0 ≤ shortIntervalMoment (H + 1) f X 2 := by
  by_cases hX : 0 < X
  · exact sum_nonneg fun _ _ => mul_nonneg (by positivity) (sq_nonneg _)
  · have hfloor : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
    simp [shortIntervalMoment, hfloor]

theorem shortInterval_fourth_bound (H : ℕ) (f : ℕ → ℝ) (X C : ℝ) (hX : 0 < X)
    (hfourth : initialMean (fun n => (f n - primeCenter f X) ^ 4) X ≤ C) :
    shortIntervalMoment (H + 1) f X 4 ≤ C := by
  have hc := backward_fourth_contraction (Icc (H + 1) ⌊X⌋₊) (H + 1) ⌊X⌋₊ (by omega)
    (fun n hn => mem_Icc.1 hn) (fun n => f n - primeCenter f X)
  simp_rw [backwardWindowAverage_sub_const (H + 1) (by omega)] at hc
  unfold shortIntervalMoment
  rw [← mul_sum]
  apply le_trans (mul_le_mul_of_nonneg_left hc (by positivity))
  simpa [initialMean, div_eq_mul_inv, mul_comm] using hfourth

theorem shortInterval_second_bound (H : ℕ) (f : ℕ → ℝ) (X C : ℝ) (hX : 0 < X)
    (hfourth : shortIntervalMoment (H + 1) f X 4 ≤ C) :
    shortIntervalMoment (H + 1) f X 2 ≤ C + 1 := by
  simpa [shortIntervalMoment] using weighted_second_moment_bound
    (Icc (H + 1) ⌊X⌋₊) (fun _ => 1 / X)
    (fun n => backwardWindowAverage (H + 1) f n - primeCenter f X)
    (fun _ _ => by positivity) 1 C (by norm_num)
    (by simpa using prefix_weight_mass H X 1 hX (by norm_num)) hfourth

theorem shortInterval_prefix_bound (H : ℕ) (f : ℕ → ℝ) (X C δ : ℝ)
    (hX : 0 < X) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hfourth : shortIntervalMoment (H + 1) f X 4 ≤ C) :
    (∑ n ∈ Icc (H + 1) ⌊δ * X⌋₊, (1 / X) *
      (backwardWindowAverage (H + 1) f n - primeCenter f X) ^ 2) ≤ sqrt (δ * C) := by
  apply restricted_second_moment_bound (Icc (H + 1) ⌊δ * X⌋₊) (Icc (H + 1) ⌊X⌋₊)
    (fun _ => 1 / X) (fun n => backwardWindowAverage (H + 1) f n - primeCenter f X)
    (Icc_subset_Icc le_rfl (Nat.floor_le_floor (mul_le_of_le_one_left hX.le hδ1)))
    (fun _ _ => by positivity) δ C hδ (prefix_weight_mass H X δ hX hδ) hfourth


def dyadicSecondMoment (H : ℕ) (f : ℕ → ℝ) (Y : ℝ) : ℝ :=
  ∑ n ∈ dyadicIndices Y, (2 / Y) *
    (backwardWindowAverage H f n - primeCenter f Y) ^ 2

theorem dyadicSecondMoment_nonneg (H : ℕ) (f : ℕ → ℝ) (Y : ℝ) :
    0 ≤ dyadicSecondMoment H f Y :=
  sum_nonneg fun _ hn => mul_nonneg (div_nonneg (by norm_num) (dyadic_member_pos hn).le) (sq_nonneg _)

theorem dyadic_global_center_bound (H : ℕ) (f : ℕ → ℝ) (X δ : ℝ)
    (hX : 0 < X) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ n ∈ dyadicIndices (δ * X), (1 / X) *
      (backwardWindowAverage H f n - primeCenter f X) ^ 2) ≤
      dyadicSecondMoment H f (δ * X) +
        2 * (primeCenter f X - primeCenter f (δ * X)) ^ 2 := by
  have hY : 0 < δ * X := mul_pos hδ hX
  have hc : 2 / X ≤ 2 / (δ * X) :=
    div_le_div_of_nonneg_left (by norm_num) hY (mul_le_of_le_one_left hX.le hδ1)
  calc
    _ ≤ ∑ n ∈ dyadicIndices (δ * X), (2 / (δ * X)) *
        ((backwardWindowAverage H f n - primeCenter f (δ * X)) ^ 2 +
          (primeCenter f X - primeCenter f (δ * X)) ^ 2) := by
      apply sum_le_sum
      intro n _
      have hs : (backwardWindowAverage H f n - primeCenter f X) ^ 2 ≤
          2 * ((backwardWindowAverage H f n - primeCenter f (δ * X)) ^ 2 +
            (primeCenter f X - primeCenter f (δ * X)) ^ 2) := by
        nlinarith [sq_nonneg (backwardWindowAverage H f n + primeCenter f X - 2 * primeCenter f (δ * X))]
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1 / X by positivity)
      have hk := mul_le_mul_of_nonneg_right hc
        (show 0 ≤ (backwardWindowAverage H f n - primeCenter f (δ * X)) ^ 2 +
          (primeCenter f X - primeCenter f (δ * X)) ^ 2 by positivity)
      apply hh.trans
      convert! hk using 1
      ring
    _ = dyadicSecondMoment H f (δ * X) +
        (∑ _n ∈ dyadicIndices (δ * X), 2 / (δ * X)) *
          (primeCenter f X - primeCenter f (δ * X)) ^ 2 := by
      simp only [mul_add, sum_add_distrib, sum_mul, dyadicSecondMoment]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (dyadic_weight_mass (δ * X)) (sq_nonneg _))

theorem shortInterval_dyadic_cover (H J : ℕ) (f : ℕ → ℝ) (X C : ℝ)
    (hX : 0 < X) (hfourth : shortIntervalMoment (H + 1) f X 4 ≤ C) :
    shortIntervalMoment (H + 1) f X 2 ≤
      (∑ j ∈ range J, dyadicSecondMoment (H + 1) f (dyadicRatio j * X)) +
      (∑ j ∈ range J, 2 * (primeCenter f X - primeCenter f (dyadicRatio j * X)) ^ 2) +
        sqrt (dyadicRatio J * C) := by
  have hcov := finite_dyadic_cover (H + 1) J X
    (fun n => (1 / X) * (backwardWindowAverage (H + 1) f n - primeCenter f X) ^ 2)
    (fun _ => by positivity)
  have hbands := sum_le_sum (fun j (_ : j ∈ range J) =>
    dyadic_global_center_bound (H + 1) f X (dyadicRatio j) hX (dyadicRatio_pos j) (dyadicRatio_le_one j))
  rw [sum_add_distrib] at hbands
  exact hcov.trans (add_le_add hbands (shortInterval_prefix_bound H f X C (dyadicRatio J)
    hX (dyadicRatio_pos J).le (dyadicRatio_le_one J) hfourth))

end

end Erdos1122
