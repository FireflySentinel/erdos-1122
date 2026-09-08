import Erdos1122.StrongFourthMoment
import Erdos1122.BackwardMoments
import Erdos1122.ShortIntervals

/-! # Lemma 2.1 on each fixed dyadic band, for a varying family -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

def dyadicIndices (Y : ℝ) : Finset ℕ := Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊

theorem dyadic_member_pos {Y : ℝ} {n : ℕ} (hn : n ∈ dyadicIndices Y) : 0 < Y := by
  have h := mem_Ioc.1 hn
  have hfloor : 0 < ⌊Y⌋₊ := by omega
  have := (Nat.one_le_floor_iff Y).1 hfloor
  linarith

theorem dyadic_weight_mass (Y : ℝ) : (∑ _n ∈ dyadicIndices Y, 2 / Y) ≤ 2 := by
  by_cases hY : 0 < Y
  · have hcard : ((dyadicIndices Y).card : ℝ) ≤ Y := by
      apply le_trans _ (Nat.floor_le hY.le)
      simp only [dyadicIndices, Nat.card_Ioc]
      exact_mod_cast Nat.sub_le ⌊Y⌋₊ ⌊Y / 2⌋₊
    simp only [sum_const, nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right hcard (show 0 ≤ 2 / Y by positivity)
    have he : Y * (2 / Y) = 2 := by field_simp
    linarith
  · have he : dyadicIndices Y = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro n hn
      exact hY (dyadic_member_pos hn)
    simp [he]

theorem dyadic_window_indices (Y : ℝ) (H : ℕ) (hY : 2 ≤ Y)
    (hH : (H : ℝ) ≤ Y / 100) :
    ∀ n ∈ dyadicIndices Y, H ≤ n ∧ n ≤ ⌊Y⌋₊ := by
  intro n hn
  have h := mem_Ioc.1 hn
  have hnY : Y / 2 < (n : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ Y / 2)).1 h.1
  refine ⟨?_, h.2⟩
  have hh : (H : ℝ) ≤ n := by linarith
  exact_mod_cast hh

def mangerelWindowError (H : ℕ) : ℝ := sqrt (log (log H) / log H)
def mangerelCutoffError (Y : ℝ) : ℝ := (log Y) ^ (-(1 : ℝ) / 800)

theorem mangerelWindowError_tendsto : Tendsto mangerelWindowError atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℕ => log H) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun H : ℕ => log (log H) / log H) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  unfold mangerelWindowError
  simpa using hratio.sqrt

theorem mangerelCutoffError_tendsto : Tendsto mangerelCutoffError atTop (𝓝 0) := by
  unfold mangerelCutoffError
  simpa [neg_div, Function.comp_def] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 800)).comp tendsto_log_atTop

theorem dyadic_centered_fourth_bound (f : ℕ → ℝ) (Y : ℝ) (H : ℕ)
    (hY : 2 ≤ Y) (hHpos : 0 < H) (hH : (H : ℝ) ≤ Y / 100) (C : ℝ)
    (hfourth : initialMean (fun n => (f n - primeCenter f Y) ^ 4) Y ≤ C) :
    (∑ n ∈ dyadicIndices Y, (2 / Y) *
      (backwardWindowAverage H f n - primeCenter f Y) ^ 4) ≤ 2 * C := by
  have hYpos : 0 < Y := by linarith
  have hc := backward_fourth_contraction (dyadicIndices Y) H ⌊Y⌋₊ hHpos
    (dyadic_window_indices Y H hY hH) (fun n => f n - primeCenter f Y)
  simp_rw [backwardWindowAverage_sub_const H hHpos] at hc
  rw [← mul_sum]
  apply le_trans (mul_le_mul_of_nonneg_left hc (by positivity))
  unfold initialMean at hfourth
  have hh := mul_le_mul_of_nonneg_left hfourth (by norm_num : (0 : ℝ) ≤ 2)
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

theorem dyadic_centered_first_bound (hM : Mangerel) (L V : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ Y : ℝ, 2 ≤ Y →
      (∀ p ∈ Nat.primesLE ⌊Y⌋₊, |f p| ≤ L) → primeMoment f Y 2 ≤ V →
      ∀ H : ℕ, 10 ≤ H → (H : ℝ) ≤ Y / 100 →
      (∑ n ∈ dyadicIndices Y, (2 / Y) *
        |backwardWindowAverage H f n - primeCenter f Y|) ≤
        A * mangerelWindowError H + A * mangerelCutoffError Y +
          4 * L * (Nat.primeCounting ⌊Y⌋₊ : ℝ) / Y := by
  obtain ⟨A, hA, hM⟩ := hM
  refine ⟨A * sqrt (2 * V), by positivity, ?_⟩
  intro f hf Y hY hcoeff hmass H hH hHY
  have hYpos : 0 < Y := by linarith
  have hlogY : 0 < log Y := log_pos (by linarith)
  have hb := (hf.primePowerMoment_le Y 2).trans (mul_le_mul_of_nonneg_left hmass (by norm_num))
  have hfirst := hM f hf.isAdditive Y hY H hH hHY
  have hcenter := hf.dyadic_center_error_le Y L hYpos hcoeff
  have hroot := sqrt_le_sqrt hb
  have herrpos : 0 ≤ mangerelWindowError H + mangerelCutoffError Y := by
    unfold mangerelWindowError mangerelCutoffError
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hroot (mul_nonneg hA.le herrpos)
  have hcomp : (∑ n ∈ dyadicIndices Y, (2 / Y) *
      |backwardWindowAverage H f n - primeCenter f Y|) ≤
      dyadicMean (fun n => |backwardWindowAverage H f n - dyadicMean f Y|) Y +
        2 * |dyadicMean f Y - primeCenter f Y| := by
    calc
      _ ≤ ∑ n ∈ dyadicIndices Y, (2 / Y) *
          (|backwardWindowAverage H f n - dyadicMean f Y| + |dyadicMean f Y - primeCenter f Y|) := by
        exact sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
          (abs_sub_le _ _ _) (by positivity)
      _ = dyadicMean (fun n => |backwardWindowAverage H f n - dyadicMean f Y|) Y +
          (∑ _n ∈ dyadicIndices Y, 2 / Y) * |dyadicMean f Y - primeCenter f Y| := by
        simp only [mul_add, sum_add_distrib, sum_mul, dyadicMean, dyadicIndices, mul_sum]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right (dyadic_weight_mass Y) (abs_nonneg _))
  change _ ≤ A * (mangerelWindowError H + mangerelCutoffError Y) * sqrt (primePowerMoment f Y 2) at hfirst
  simp only [div_eq_mul_inv] at hfirst hscaled hcenter hcomp ⊢
  nlinarith only [hfirst, hscaled, hcenter, hcomp]

/-- The family is indexed by the original cutoff `X`, even on the band
ending at `δ X`. Mangerel's constant remains uniform in that family. -/
theorem dyadic_short_interval_limit (hM : Mangerel)
    (z : ℝ → ℕ → ℝ) (L V : ℝ) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hz : ∀ X, IsStronglyAdditive (z X))
    (hcoeff : ∀ X p, p.Prime → |z X p| ≤ L)
    (hmass : ∀ X, 2 ≤ X → primeMoment (z X) X 2 ≤ V)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun H : ℕ => limsup (fun X : ℝ =>
      ∑ n ∈ dyadicIndices (δ * X), (2 / (δ * X)) *
        (backwardWindowAverage (H + 1) (z X) n - primeCenter (z X) (δ * X)) ^ 2) atTop)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hfourth⟩ := stronglyAdditive_fourth_moment L V hL hV
  obtain ⟨A, hA, hfirst⟩ := dyadic_centered_first_bound hM L V
  have hscale : Tendsto (fun X : ℝ => δ * X) atTop atTop := tendsto_id.const_mul_atTop hδ
  let a : ℕ → ℝ := fun H => A * mangerelWindowError (H + 1)
  let b : ℝ → ℝ := fun X => A * mangerelCutoffError (δ * X) +
    4 * L * (Nat.primeCounting ⌊δ * X⌋₊ : ℝ) / (δ * X)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa [a] using (mangerelWindowError_tendsto.comp (tendsto_add_atTop_nat 1)).const_mul A
  have hb : Tendsto b atTop (𝓝 0) := by
    convert! ((mangerelCutoffError_tendsto.comp hscale).const_mul A).add
      ((primeCounting_ratio_tendsto_zero.comp hscale).const_mul (4 * L)) using 1
    · ext X
      dsimp [b]
      ring
    · simp
  refine uniform_first_fourth_moment_transfer (dyadicIndices ∘ fun X => δ * X)
    (fun X _ => 2 / (δ * X))
    (fun H X n => backwardWindowAverage (H + 1) (z X) n - primeCenter (z X) (δ * X))
    2 (2 * C) (by norm_num)
    (fun X n hn => div_nonneg (by norm_num) (dyadic_member_pos hn).le)
    (fun X => dyadic_weight_mass (δ * X)) ?_ a b 10 ha hb ?_
  · intro H
    filter_upwards [hscale.eventually (eventually_ge_atTop (max 2 (100 * ((H + 1 : ℕ) : ℝ)))),
      eventually_ge_atTop (2 : ℝ)] with X hY hX
    have hY2 : 2 ≤ δ * X := (le_max_left _ _).trans hY
    have hHY : ((H + 1 : ℕ) : ℝ) ≤ (δ * X) / 100 := by linarith [le_max_right 2 (100 * ((H + 1 : ℕ) : ℝ))]
    exact dyadic_centered_fourth_bound (z X) (δ * X) (H + 1) hY2 (by omega) hHY C
      (hfourth (z X) (hz X) (δ * X) hY2 (fun p hp => hcoeff X p (Nat.prime_of_mem_primesLE hp))
        ((primeMoment_mono (z X) 2 (mul_le_of_le_one_left (by linarith) hδ1)).trans (hmass X hX)))
  · intro H hH
    filter_upwards [hscale.eventually (eventually_ge_atTop (max 2 (100 * ((H + 1 : ℕ) : ℝ)))),
      eventually_ge_atTop (2 : ℝ)] with X hY hX
    have hY2 : 2 ≤ δ * X := (le_max_left _ _).trans hY
    have hHY : ((H + 1 : ℕ) : ℝ) ≤ (δ * X) / 100 := by linarith [le_max_right 2 (100 * ((H + 1 : ℕ) : ℝ))]
    simpa only [a, b, add_assoc, Function.comp_apply] using hfirst (z X) (hz X) (δ * X) hY2 (fun p hp => hcoeff X p (Nat.prime_of_mem_primesLE hp))
      ((primeMoment_mono (z X) 2 (mul_le_of_le_one_left (by linarith) hδ1)).trans (hmass X hX))
      (H + 1) (by omega) hHY

end

end Erdos1122
