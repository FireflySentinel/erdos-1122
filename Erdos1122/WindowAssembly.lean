import Erdos1122.ObservableVariation

/-! # The final window comparison, with the cutoff limit taken first -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

theorem backwardWindowAverage_sub (H : ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    backwardWindowAverage H (fun m => f m - g m) n =
      backwardWindowAverage H f n - backwardWindowAverage H g n := by
  simp [backwardWindowAverage, sum_sub_distrib, sub_div]

/-- The four-term identity and Jensen contraction on the exact positive
backward windows of the manuscript. -/
theorem window_variance_band (z Y : ℕ → ℝ) (a X : ℝ) (H : ℕ)
    (hH : 0 < H) (hX : 0 < X) :
    (∑ n ∈ Icc H ⌊X⌋₊, (z n - primeCenter z X) ^ 2) / X ≤
      8 * initialMean (fun n => (Y n - (z n - a)) ^ 2) X +
      4 * ((∑ n ∈ Icc H ⌊X⌋₊, (Y n - backwardWindowAverage H Y n) ^ 2) / X) +
      4 * shortIntervalMoment H z X 2 := by
  let T := Icc H ⌊X⌋₊
  have hT : ∀ n ∈ T, H ≤ n ∧ n ≤ ⌊X⌋₊ := fun _ hn => mem_Icc.1 hn
  have hsub : T ⊆ Ioc 0 ⌊X⌋₊ := by
    intro n hn
    exact mem_Ioc.2 ⟨lt_of_lt_of_le hH (hT n hn).1, (hT n hn).2⟩
  have hfirst : (∑ n ∈ T, ((z n - a) - Y n) ^ 2) ≤
      ∑ n ∈ Ioc 0 ⌊X⌋₊, (Y n - (z n - a)) ^ 2 := by
    have he (n : ℕ) : ((z n - a) - Y n) ^ 2 = (Y n - (z n - a)) ^ 2 := by ring
    simp_rw [he]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hthird := backward_second_contraction T H ⌊X⌋₊ hH hT (fun n => Y n - (z n - a))
  simp only [backwardWindowAverage_sub, backwardWindowAverage_sub_const H hH] at hthird
  have hsum := sum_le_sum (s := T) (fun n _ => average_comparison_square (z n - a) (Y n)
    (backwardWindowAverage H z n - a) (backwardWindowAverage H Y n) (primeCenter z X - a))
  simp only [sub_sub_sub_cancel_right, sum_add_distrib, ← mul_sum] at hsum
  have hh : (∑ n ∈ T, (z n - primeCenter z X) ^ 2) ≤
      8 * (∑ n ∈ Ioc 0 ⌊X⌋₊, (Y n - (z n - a)) ^ 2) +
      4 * (∑ n ∈ T, (Y n - backwardWindowAverage H Y n) ^ 2) +
      4 * (∑ n ∈ T, (backwardWindowAverage H z n - primeCenter z X) ^ 2) := by
    linarith only [hsum, hfirst, hthird]
  apply (div_le_div_of_nonneg_right hh hX.le).trans_eq
  unfold initialMean shortIntervalMoment
  rw [← mul_sum]
  dsimp only [T]
  ring

/-- The omitted finite prefix is bounded by its weight and the fourth
moment. Its upper bound tends to zero with `H` fixed. -/
theorem window_variance_full (z Y : ℕ → ℝ) (a X C : ℝ) (H : ℕ)
    (hH : 0 < H) (hX : 0 < X) (hHX : (H : ℝ) ≤ X)
    (hfourth : initialMean (fun n => (z n - primeCenter z X) ^ 4) X ≤ C) :
    initialMean (fun n => (z n - primeCenter z X) ^ 2) X ≤
      8 * initialMean (fun n => (Y n - (z n - a)) ^ 2) X +
      4 * ((∑ n ∈ Icc H ⌊X⌋₊, (Y n - backwardWindowAverage H Y n) ^ 2) / X) +
      4 * shortIntervalMoment H z X 2 + sqrt (((H : ℝ) / X) * C) := by
  have hHN : H ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX.le).2 hHX
  have hsub : Ico 1 H ⊆ Ioc 0 ⌊X⌋₊ := by
    intro n hn
    have := mem_Ico.1 hn
    exact mem_Ioc.2 ⟨by omega, by omega⟩
  have hm : (∑ _n ∈ Ico 1 H, 1 / X) ≤ (H : ℝ) / X := by
    simp only [sum_const, nsmul_eq_mul, Nat.card_Ico]
    have hh : ((H - 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H 1
    exact (mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 1 / X)).trans_eq (by ring)
  have h4 : (∑ n ∈ Ioc 0 ⌊X⌋₊, (1 / X) * (z n - primeCenter z X) ^ 4) ≤ C := by
    rw [← mul_sum]
    simpa only [initialMean, div_eq_mul_inv, one_mul, mul_comm, mul_one] using hfourth
  have hp := restricted_second_moment_bound (Ico 1 H) (Ioc 0 ⌊X⌋₊)
    (fun _ => 1 / X) (fun n => z n - primeCenter z X) hsub
    (fun _ _ => by positivity) ((H : ℝ) / X) C (by positivity) hm h4
  have he : Ioc 0 ⌊X⌋₊ = Ico 1 H ∪ Icc H ⌊X⌋₊ := by
    ext n
    simp only [mem_Ioc, mem_union, mem_Ico, mem_Icc]
    omega
  have hd : Disjoint (Ico 1 H) (Icc H ⌊X⌋₊) := by
    apply disjoint_left.2
    intro n hn hm
    have := mem_Ico.1 hn
    have := mem_Icc.1 hm
    omega
  have hb := window_variance_band z Y a X H hH hX
  rw [← mul_sum] at hp
  unfold initialMean
  conv_lhs => rw [he, sum_union hd, add_div]
  have heq : (1 / X) * (∑ n ∈ Ico 1 H, (z n - primeCenter z X) ^ 2) =
      (∑ n ∈ Ico 1 H, (z n - primeCenter z X) ^ 2) / X := by ring
  rw [heq] at hp
  dsimp only [initialMean] at hb
  linarith only [hp, hb]

/-- The last named arithmetic hypothesis follows from Elliott, with no
additional uniformity or interchange of limits. -/
theorem window_assembly_of_elliott (hE : Elliott) : WindowAssembly := by
  intro f _hf hdec K M hK hM _hMq N hdiscrep hshort
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨C, hC, hfourth⟩ := stronglyAdditive_fourth_moment hE K (K ^ 2 * M) hK0 (by positivity)
  have h4 : ∀ᶠ X in atTop,
      initialMean (fun n => (N.comparison K X n - primeCenter (N.comparison K X) X) ^ 4) X ≤ C := by
    filter_upwards [N.comparison_mass K hK.le, eventually_ge_atTop (2 : ℝ)] with X hm hX
    exact hfourth _ (N.comparison_stronglyAdditive K X) X hX
      (fun p hp => N.comparison_coeff K hK0 X p (Nat.prime_of_mem_primesLE hp)) hm
  apply variance_limsup_bound (N.variance K) (N.discrepancy K)
    (N.observableWindowMoment K) (fun H X => shortIntervalMoment H (N.comparison K X) X 2)
    (fun H X => sqrt (((H : ℝ) / X) * C))
    (fun X => initialMean_square_nonneg _ X) hdiscrep
    ?_ (N.observable_window_tendsto K hK0 hdec) ?_ hshort ?_
  · intro H hH
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hH.ne'
    refine ⟨C + 1, ?_⟩
    change ∀ᶠ X in atTop, shortIntervalMoment (j + 1) (N.comparison K X) X 2 ≤ C + 1
    filter_upwards [h4, eventually_gt_atTop (0 : ℝ)] with X hh hX
    exact shortInterval_second_bound j _ X C hX (shortInterval_fourth_bound j _ X C hX hh)
  · intro H _hH
    simpa only [zero_mul, sqrt_zero, id_eq] using ((tendsto_id.const_div_atTop (H : ℝ)).mul_const C).sqrt
  · intro H hH
    filter_upwards [h4, eventually_ge_atTop (H : ℝ), eventually_gt_atTop (0 : ℝ)] with X hh hHX hX
    exact window_variance_full (N.comparison K X) (N.observable K X) (N.offset X) X C H hH hX hHX hh

end

end Erdos1122
