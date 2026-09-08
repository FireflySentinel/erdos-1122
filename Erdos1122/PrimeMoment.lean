import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # The logarithmically weighted prime sum used in Lemma 3.1 -/

namespace Erdos1122

open Finset Real MeasureTheory intervalIntegral

noncomputable section

def primeLogMoment (y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log p / p

theorem primeLogMoment_partial_summation (y : ℝ) (hy : 2 ≤ y) :
    primeLogMoment y = Chebyshev.theta y / y +
      ∫ t in 2..y, Chebyshev.theta t / t ^ 2 := by
  let a : ℕ → ℝ := fun n => if n.Prime then log n else 0
  have hrewrite : primeLogMoment y = ∑ n ∈ Icc 0 ⌊y⌋₊, (n : ℝ)⁻¹ * a n := by
    unfold primeLogMoment
    rw [Nat.primesLE_eq_filter_Icc_zero, sum_filter]
    apply sum_congr rfl
    intro n _
    simp only [a]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [hrewrite, sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ => t⁻¹)
    (by simp [a]) (by simp [a])]
  · rw [← intervalIntegral.integral_of_le hy]
    simp only [deriv_inv]
    have hsum (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, a n) = Chebyshev.theta t := by
      simp only [a, Chebyshev.theta_eq_sum_Icc, sum_filter]
    simp_rw [hsum]
    have heq : (∫ t in 2..y, -(t ^ 2)⁻¹ * Chebyshev.theta t) =
        -(∫ t in 2..y, Chebyshev.theta t / t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      apply integral_congr
      intro t _
      simp [div_eq_mul_inv, mul_comm]
    rw [heq]
    simp [div_eq_mul_inv, mul_comm]
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop
  · have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 2 y) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
      exact ContinuousAt.continuousWithinAt (by fun_prop)
    convert! hc.integrableOn_Icc (μ := volume) using 1
    ext t
    exact deriv_inv

/-- The prime moment bound using mathlib’s proved Chebyshev inequality. -/
theorem primeLogMoment_le (y : ℝ) (hy : 2 ≤ y) :
    primeLogMoment y ≤ (log 4) * (1 + log y) := by
  have hA : 0 ≤ log (4 : ℝ) := (log_pos (by norm_num)).le
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc 2 y) := by
    rw [Set.uIcc_of_le hy]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t / t ^ 2) volume 2 y := by
    simpa only [div_eq_mul_inv] using Chebyshev.theta_mono.intervalIntegrable.mul_continuousOn hcont
  have hc : ContinuousOn (fun t : ℝ => (log 4) / t) (Set.uIcc 2 y) := by
    rw [Set.uIcc_of_le hy]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hint := integral_mono_on hy hi hc.intervalIntegrable (fun t ht => by
    have ht0 : 0 < t := by linarith [ht.1]
    have hh := div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])) (sq_nonneg t)
    have heq : (log 4) * t / t ^ 2 = (log 4) / t := by field_simp
    exact hh.trans_eq heq)
  have heval : (∫ t in 2..y, (log 4) / t) = (log 4) * log (y / 2) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by linarith)]
    rfl
  rw [heval] at hint
  have hfront : Chebyshev.theta y / y ≤ (log 4) := by
    exact (div_le_iff₀ (by linarith : 0 < y)).2 (Chebyshev.theta_le_log4_mul_x (by linarith))
  rw [primeLogMoment_partial_summation y hy]
  have hlog : log (y / 2) ≤ log y := by
    rw [log_div (by linarith) (by norm_num)]
    have := log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog hA
  linarith

end

end Erdos1122
