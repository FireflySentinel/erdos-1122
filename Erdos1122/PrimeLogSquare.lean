import Erdos1122.PrimeMoment
import Erdos1122.Projection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The prime logarithmic second moment from Chebyshev -/

namespace Erdos1122

open Finset Real Filter Topology MeasureTheory intervalIntegral

set_option autoImplicit false
noncomputable section

/-- A fixed positive linear lower bound, deduced from mathlib's explicit
Chebyshev inequality. -/
theorem theta_eventually_ge_linear :
    ∀ᶠ X : ℝ in atTop, (log 2 / 2) * X ≤ Chebyshev.theta X := by
  have hroot : Tendsto (fun X : ℝ => sqrt X * log X / X) atTop (𝓝 0) := by
    have hlim : Tendsto (fun X : ℝ => log X / sqrt X) atTop (𝓝 0) := by
      simpa only [sqrt_eq_rpow] using
        (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hs : sqrt X ≠ 0 := (sqrt_pos.2 hX).ne'
    apply (div_eq_div_iff hs hX.ne').2
    nlinarith only [congrArg (fun t : ℝ => t * log X) (sq_sqrt hX.le)]
  have herr : Tendsto (fun X : ℝ => (2 * log 2 + log X + 2 * sqrt X * log X) / X)
      atTop (𝓝 0) := by
    convert! ((tendsto_id.const_div_atTop (2 * log (2 : ℝ))).add
      isLittleO_log_id_atTop.tendsto_div_nhds_zero).add (hroot.const_mul 2) using 1
    · ext X
      dsimp
      ring
    · simp
  have hd : 0 < log (2 : ℝ) / 2 := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), herr.eventually (eventually_lt_nhds hd)] with X hX he
  have hXp : 0 < X := by linarith
  have hlog : log (X + 2) ≤ log 2 + log X := by
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) hXp.ne']
    exact log_le_log (by linarith) (by linarith)
  have ht := Chebyshev.theta_ge' (by linarith : 1 ≤ X)
  have hh := (div_lt_iff₀ hXp).1 he
  linarith

def primeLogSquare (X : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊X⌋₊, (log p) ^ 2 / (p : ℝ)

private theorem log_div_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => log x / x) ((1 - log t) / t ^ 2) t := by
  convert! (hasDerivAt_log ht.ne').div (hasDerivAt_id t) ht.ne' using 1
  simp only [id_eq]
  field_simp

private theorem logSquare_sum_rewrite (X : ℝ) :
    primeLogSquare X = ∑ n ∈ Icc 0 ⌊X⌋₊,
      (log n / (n : ℝ)) * (if n.Prime then log n else 0) := by
  unfold primeLogSquare
  rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  apply sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem primeLogSquare_partial_summation (X Y : ℝ) (hY : 2 ≤ Y) (hYX : Y ≤ X) :
    primeLogSquare X - primeLogSquare Y =
      Chebyshev.theta X * log X / X - Chebyshev.theta Y * log Y / Y +
        ∫ t in Y..X, Chebyshev.theta t * ((log t - 1) / t ^ 2) := by
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
  rw [logSquare_sum_rewrite, logSquare_sum_rewrite, he, sum_union hd, add_sub_cancel_left]
  have hc : ContinuousOn (fun t : ℝ => (1 - log t) / t ^ 2) (Set.Icc Y X) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hsq : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hder (t : ℝ) (ht : t ∈ Set.Icc Y X) := log_div_deriv t (by linarith [ht.1])
  rw [sum_mul_eq_sub_sub_integral_mul a (by linarith : 0 ≤ Y) hYX
    (fun t ht => (hder t ht).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun t ht => (hder t ht).deriv.symm) measurableSet_Icc)]
  rw [← intervalIntegral.integral_of_le hYX]
  have hsum (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, a n) = Chebyshev.theta t := by
    simp only [a, Chebyshev.theta_eq_sum_Icc, sum_filter]
  simp_rw [hsum]
  have hi : (∫ t in Y..X, deriv (fun x : ℝ => log x / x) t * Chebyshev.theta t) =
      -(∫ t in Y..X, Chebyshev.theta t * ((log t - 1) / t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    apply integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc Y X := by simpa [Set.uIcc_of_le hYX] using ht
    dsimp only
    rw [(hder t ht').deriv]
    ring
  rw [hi]
  ring


/-- Only a lower bound of order `(log X)^2` is needed in (5.10).
This theorem uses Chebyshev alone, with no prime-number or Mertens theorem. -/
theorem primeLogSquare_eventually_lower :
    ∀ᶠ X : ℝ in atTop, (log 2 / 8) * (log X) ^ 2 ≤ primeLogSquare X := by
  let d : ℝ := log 2 / 2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨A, hA⟩ := eventually_atTop.1 theta_eventually_ge_linear
  let Y : ℝ := max A (exp 2)
  have hYexp : exp 2 ≤ Y := le_max_right _ _
  have hY : 2 ≤ Y := by linarith [add_one_le_exp (2 : ℝ)]
  let B : ℝ := Chebyshev.theta Y * log Y / Y + d * ((log Y) ^ 2 / 2 - log Y)
  have hlower (X : ℝ) (hYX : Y ≤ X) :
      d * ((log X) ^ 2 / 2 - log X) - B ≤ primeLogSquare X := by
    have hX : 2 ≤ X := hY.trans hYX
    have hpos (t : ℝ) (ht : t ∈ Set.uIcc Y X) : 0 < t := by
      rw [Set.uIcc_of_le hYX] at ht
      linarith [ht.1]
    have hc : ContinuousOn (fun t : ℝ => (log t - 1) / t ^ 2) (Set.uIcc Y X) := by
      intro t ht
      have ht0 := (hpos t ht).ne'
      have hs := pow_ne_zero 2 ht0
      exact ContinuousAt.continuousWithinAt (by fun_prop)
    have hc' : ContinuousOn (fun t : ℝ => d * (log t - 1) / t) (Set.uIcc Y X) := by
      intro t ht
      have ht0 := (hpos t ht).ne'
      exact ContinuousAt.continuousWithinAt (by fun_prop)
    have hi := integral_mono_on (μ := volume) hYX hc'.intervalIntegrable
      (Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn hc) (fun t ht => by
        have ht0 : 0 < t := by linarith [ht.1]
        have hlog : 2 ≤ log t := by
          rw [← log_exp (2 : ℝ)]
          exact log_le_log (exp_pos _) (hYexp.trans ht.1)
        have hh := mul_le_mul_of_nonneg_right (hA t ((le_max_left _ _).trans ht.1))
          (div_nonneg (by linarith : 0 ≤ log t - 1) (sq_nonneg t))
        change d * (log t - 1) / t ≤ _
        convert! hh using 1
        dsimp [d]
        field_simp)
    have heval : (∫ t in Y..X, d * (log t - 1) / t) =
        d * ((log X) ^ 2 / 2 - log X) - d * ((log Y) ^ 2 / 2 - log Y) := by
      apply integral_eq_sub_of_hasDerivAt _ hc'.intervalIntegrable
      intro t ht
      have ht0 := (hpos t ht).ne'
      convert! (((hasDerivAt_log ht0).pow 2).div_const 2 |>.sub (hasDerivAt_log ht0)).const_mul d using 1
      field_simp
      ring
    rw [heval] at hi
    have he := primeLogSquare_partial_summation X Y hY hYX
    have hn : 0 ≤ primeLogSquare Y := by unfold primeLogSquare; positivity
    have hlogX : 0 < log X := log_pos (by linarith)
    have hp : 0 ≤ Chebyshev.theta X * log X / X := by positivity
    dsimp [B]
    linarith
  have he : Tendsto (fun X : ℝ => d / log X + B / (log X) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_log_atTop.const_div_atTop d).add
      ((tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp tendsto_log_atTop |>.const_div_atTop B)
  filter_upwards [eventually_ge_atTop Y,
    he.eventually (eventually_lt_nhds (show 0 < d / 4 by positivity))] with X hX herr
  have hlog : 0 < log X := log_pos (by linarith)
  have hh := (mul_lt_mul_of_pos_right herr (sq_pos_of_pos hlog)).le
  have hcancel : (d / log X + B / (log X) ^ 2) * (log X) ^ 2 = d * log X + B := by field_simp
  rw [hcancel] at hh
  have hlo := hlower X hX
  dsimp [d] at hh hlo
  nlinarith only [hh, hlo]

end

end Erdos1122
