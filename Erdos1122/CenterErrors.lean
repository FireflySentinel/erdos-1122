import Erdos1122.StrongAdditive
import Erdos1122.PrimeHarmonic

/-! # Centers of the actual strongly additive averages -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

theorem dyadic_floor_error_le (Y : ℝ) (hY : 0 < Y) (p : ℕ) (hp : 0 < p) :
    |(2 / Y) * ((⌊Y / (p : ℝ)⌋₊ : ℝ) - (⌊Y / (2 * (p : ℝ))⌋₊ : ℝ)) - 1 / (p : ℝ)|
      ≤ 2 / Y := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h₁ := Nat.floor_le (show 0 ≤ Y / (p : ℝ) by positivity)
  have h₂ := Nat.lt_floor_add_one (Y / (p : ℝ))
  have h₃ := Nat.floor_le (show 0 ≤ Y / (2 * (p : ℝ)) by positivity)
  have h₄ := Nat.lt_floor_add_one (Y / (2 * (p : ℝ)))
  have he : (2 / Y) * ((⌊Y / (p : ℝ)⌋₊ : ℝ) - (⌊Y / (2 * (p : ℝ))⌋₊ : ℝ)) - 1 / (p : ℝ) =
      (2 * ((⌊Y / (p : ℝ)⌋₊ : ℝ) - (⌊Y / (2 * (p : ℝ))⌋₊ : ℝ)) - Y / (p : ℝ)) / Y := by
    field_simp
  rw [he, abs_div, abs_of_pos hY]
  apply div_le_div_of_nonneg_right _ hY.le
  have he₂ : Y / (p : ℝ) = 2 * (Y / (2 * (p : ℝ))) := by ring
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem IsStronglyAdditive.dyadic_center_error_le {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) (Y L : ℝ) (hY : 0 < Y)
    (hcoeff : ∀ p ∈ Nat.primesLE ⌊Y⌋₊, |f p| ≤ L) :
    |dyadicMean f Y - primeCenter f Y| ≤ 2 * L * (Nat.primeCounting ⌊Y⌋₊ : ℝ) / Y := by
  rw [hf.dyadic_center_identity]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, |f p * ((2 / Y) *
        ((⌊Y / (p : ℝ)⌋₊ : ℝ) - (⌊Y / (2 * (p : ℝ))⌋₊ : ℝ)) - 1 / (p : ℝ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Nat.primesLE ⌊Y⌋₊, L * (2 / Y) := by
      apply sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul (hcoeff p hp) (dyadic_floor_error_le Y hY p (Nat.prime_of_mem_primesLE hp).pos)
        (abs_nonneg _) ((abs_nonneg _).trans (hcoeff p hp))
    _ = _ := by simp [Nat.primesLE_card_eq_primeCounting]; ring

theorem primeCounting_ratio_tendsto_zero :
    Tendsto (fun X : ℝ => (Nat.primeCounting ⌊X⌋₊ : ℝ) / X) atTop (𝓝 0) := by
  apply squeeze_zero' (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX; positivity)
    (g := fun X : ℝ => (log 4 + 1) / log X)
  · filter_upwards [Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop (2 : ℝ)] with X hpi hX
    have hX0 : 0 < X := by linarith
    apply (div_le_iff₀ hX0).2
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpi
  · exact tendsto_log_atTop.const_div_atTop (log 4 + 1)

theorem primeHarmonic_fixed_ratio_tendsto_zero (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun X : ℝ => primeHarmonic X - primeHarmonic (δ * X)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun X : ℝ => δ * X) atTop atTop :=
    tendsto_id.const_mul_atTop hδ
  have hlog := tendsto_log_atTop.comp hscale
  have hrat : Tendsto (fun X : ℝ => log X / log (δ * X)) atTop (𝓝 1) := by
    have hh : Tendsto (fun X : ℝ => 1 - log δ / log (δ * X)) atTop (𝓝 1) := by
      simpa using (hlog.const_div_atTop (log δ)).const_sub 1
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ), hscale.eventually (eventually_ge_atTop (2 : ℝ))] with X hX hδX
    have hX0 : X ≠ 0 := by linarith
    have hl : log (δ * X) ≠ 0 := (log_pos (by linarith)).ne'
    rw [log_mul hδ.ne' hX0] at hl ⊢
    field_simp
    ring
  have hbound : Tendsto (fun X : ℝ => log 4 *
      (log (log X / log (δ * X)) + 1 / log (δ * X))) atTop (𝓝 0) := by
    simpa using ((hrat.log (by norm_num)).add (hlog.const_div_atTop 1)).const_mul (log 4)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    apply sub_nonneg.2
    unfold primeHarmonic
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Nat.mem_primesLE.2 ⟨(Nat.mem_primesLE.1 hp).1.trans
        (Nat.floor_le_floor (mul_le_of_le_one_left hX hδ1)), (Nat.mem_primesLE.1 hp).2⟩
    · intro _ _ _
      positivity
  · filter_upwards [hscale.eventually (eventually_ge_atTop (2 : ℝ)),
      eventually_ge_atTop (0 : ℝ)] with X hδX hX
    exact primeHarmonic_difference X (δ * X) hδX (mul_le_of_le_one_left hX hδ1)

theorem primeCenter_difference_le (f : ℕ → ℝ) (X Y L : ℝ) (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (hcoeff : ∀ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ≤ L) :
    |primeCenter f X - primeCenter f Y| ≤ L * (primeHarmonic X - primeHarmonic Y) := by
  have hr := congrArg (fun P : Finset ℕ => ∑ p ∈ P, f p / (p : ℝ)) (primes_restrict X Y hY hYX)
  rw [sum_filter] at hr
  unfold primeCenter
  rw [← hr, ← sum_sub_distrib, ← primeHarmonic_tail X Y hY hYX, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  by_cases h : (p : ℝ) ≤ Y
  · simp [h, not_lt.mpr h]
  · have hp0 : (0 : ℝ) ≤ p := by positivity
    simp only [if_neg h, if_pos (lt_of_not_ge h), sub_zero, abs_div, abs_of_nonneg hp0]
    exact (div_le_div_of_nonneg_right (hcoeff p hp) hp0).trans_eq (by ring)

theorem primeCenter_fixed_ratio_tendsto_zero (z : ℝ → ℕ → ℝ) (L δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcoeff : ∀ X p, p.Prime → |z X p| ≤ L) :
    Tendsto (fun X : ℝ => primeCenter (z X) X - primeCenter (z X) (δ * X)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa using (primeHarmonic_fixed_ratio_tendsto_zero δ hδ hδ1).const_mul L)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  simpa only [Real.norm_eq_abs] using primeCenter_difference_le (z X) X (δ * X) L
    (by positivity) (mul_le_of_le_one_left hX hδ1)
    (fun p hp => hcoeff X p (Nat.prime_of_mem_primesLE hp))

end

end Erdos1122
