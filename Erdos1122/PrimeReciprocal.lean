import Erdos1122.PrimeMoment

/-! # Reciprocal prime sums from Chebyshev and Abel summation -/

namespace Erdos1122

open Finset Real MeasureTheory intervalIntegral

noncomputable section

def primeHarmonic (y : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊y⌋₊, 1 / (p : ℝ)

private theorem reciprocal_log_deriv (t : ℝ) (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => (x * log x)⁻¹)
      (-(log t + 1) / (t * log t) ^ 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (log_pos ht).ne'
  convert! ((hasDerivAt_id t).mul (hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hl) using 1
  simp only [Pi.mul_apply, id_eq]
  field_simp

private theorem harmonic_sum_rewrite (x : ℝ) :
    primeHarmonic x = ∑ n ∈ Icc 0 ⌊x⌋₊,
      ((n : ℝ) * log n)⁻¹ * (if n.Prime then log n else 0) := by
  unfold primeHarmonic
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Prime
  · simp only [if_pos hn]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne_zero
    have hl : log (n : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hn.one_lt)).ne'
    field_simp
  · simp [hn]

theorem primeHarmonic_partial_summation (X Y : ℝ) (hY : 2 ≤ Y) (hYX : Y ≤ X) :
    primeHarmonic X - primeHarmonic Y =
      Chebyshev.theta X / (X * log X) - Chebyshev.theta Y / (Y * log Y) +
        ∫ t in Y..X, Chebyshev.theta t * ((log t + 1) / (t * log t) ^ 2) := by
  let a : ℕ → ℝ := fun n => if n.Prime then log n else 0
  have he : Icc 0 ⌊X⌋₊ = Icc 0 ⌊Y⌋₊ ∪ Ioc ⌊Y⌋₊ ⌊X⌋₊ := by
    ext n
    simp only [mem_union, mem_Icc, mem_Ioc]
    have := Nat.floor_le_floor hYX
    omega
  have hd : Disjoint (Icc 0 ⌊Y⌋₊) (Ioc ⌊Y⌋₊ ⌊X⌋₊) := by
    apply disjoint_left.2
    intro n hn hm
    simp only [mem_Icc, mem_Ioc] at hn hm
    omega
  rw [harmonic_sum_rewrite, harmonic_sum_rewrite, he, sum_union hd, add_sub_cancel_left]
  have hc : ContinuousOn (fun t : ℝ => -(log t + 1) / (t * log t) ^ 2) (Set.Icc Y X) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos ht1).ne'
    have hd : (t * log t) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero ht0 hl)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hdif (t : ℝ) (ht : t ∈ Set.Icc Y X) := reciprocal_log_deriv t (by linarith [ht.1])
  rw [sum_mul_eq_sub_sub_integral_mul a (by linarith : 0 ≤ Y) hYX
    (fun t ht => (hdif t ht).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun t ht => (hdif t ht).deriv.symm) measurableSet_Icc)]
  rw [← intervalIntegral.integral_of_le hYX]
  have hsum (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, a n) = Chebyshev.theta t := by
    simp only [a, Chebyshev.theta_eq_sum_Icc, sum_filter]
  simp_rw [hsum]
  have hi : (∫ t in Y..X, deriv (fun x : ℝ => (x * log x)⁻¹) t * Chebyshev.theta t) =
      -(∫ t in Y..X, Chebyshev.theta t * ((log t + 1) / (t * log t) ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc Y X := by simpa [Set.uIcc_of_le hYX] using ht
    dsimp only
    rw [(hdif t ht').deriv]
    ring
  rw [hi]
  simp [div_eq_mul_inv, mul_comm]

/-- The reciprocal-prime estimate used below is unconditional. -/
theorem primeHarmonic_difference (X Y : ℝ) (hY : 2 ≤ Y) (hYX : Y ≤ X) :
    primeHarmonic X - primeHarmonic Y ≤
      log 4 * (log (log X / log Y) + 1 / log Y) := by
  have hX : 2 ≤ X := hY.trans hYX
  have hlogX : 0 < log X := log_pos (by linarith)
  have hlogY : 0 < log Y := log_pos (by linarith)
  have hD : 0 ≤ log (4 : ℝ) := (log_pos (by norm_num)).le
  have cont (f : ℝ → ℝ) (hf : ∀ t, 2 ≤ t → ContinuousAt f t) :
      ContinuousOn f (Set.uIcc Y X) := by
    intro t ht
    rw [Set.uIcc_of_le hYX] at ht
    exact (hf t (hY.trans ht.1)).continuousWithinAt
  have hc : ContinuousOn (fun t : ℝ => (log t + 1) / (t * log t) ^ 2) (Set.uIcc Y X) := by
    apply cont
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos (by linarith)).ne'
    have hd : (t * log t) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero ht0 hl)
    fun_prop
  have h₁ : ContinuousOn (fun t : ℝ => t⁻¹ / log t) (Set.uIcc Y X) := by
    apply cont
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos (by linarith)).ne'
    fun_prop
  have h₂ : ContinuousOn (fun t : ℝ => t⁻¹ / log t ^ 2) (Set.uIcc Y X) := by
    apply cont
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have hl : log t ≠ 0 := (log_pos (by linarith)).ne'
    have hd : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    fun_prop
  have hb := integral_mono_on (μ := volume) hYX
    (Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn hc)
    ((h₁.add h₂).const_mul (log 4)).intervalIntegrable (fun t ht => by
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : t ≠ 0 := by linarith
      have hl : log t ≠ 0 := (log_pos ht1).ne'
      calc
        _ ≤ (log 4 * t) * ((log t + 1) / (t * log t) ^ 2) :=
          mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by linarith))
            (div_nonneg (by linarith [log_pos ht1]) (sq_nonneg _))
        _ = log 4 * (t⁻¹ / log t + t⁻¹ / log t ^ 2) := by field_simp)
  simp only [Pi.add_apply] at hb
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add h₁.intervalIntegrable h₂.intervalIntegrable,
    integral_inv_div_log (by linarith) (by linarith),
    integral_inv_div_log_sq (by linarith) (by linarith)] at hb
  have hfront : Chebyshev.theta X / (X * log X) ≤ log 4 / log X := by
    calc
      _ ≤ (log 4 * X) / (X * log X) := div_le_div_of_nonneg_right
        (Chebyshev.theta_le_log4_mul_x (by linarith)) (by positivity)
      _ = _ := by field_simp
  have hback : 0 ≤ Chebyshev.theta Y / (Y * log Y) := by positivity
  rw [primeHarmonic_partial_summation X Y hY hYX,
    log_div (log_pos (by linarith : 1 < X)).ne' (log_pos (by linarith : 1 < Y)).ne']
  simp only [div_eq_mul_inv] at hb hfront hback ⊢
  linarith

end

end Erdos1122
