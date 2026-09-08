import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# First- and fourth-moment interpolation

A polynomial form of the interpolation inequality used in Lemma 2.1.
The inequality holds for arbitrary nonnegative weights and real inputs.
-/

namespace Erdos1122

open Finset

noncomputable section

theorem weighted_moment_interpolation {ι : Type*} (t : Finset ι)
    (w a : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i) :
    (∑ i ∈ t, w i * (a i) ^ 2) ^ 3
      ≤ (∑ i ∈ t, w i * |a i|) ^ 2 * ∑ i ∈ t, w i * (a i) ^ 4 := by
  let S₁ := ∑ i ∈ t, w i * |a i|
  let S₂ := ∑ i ∈ t, w i * (a i) ^ 2
  let S₃ := ∑ i ∈ t, w i * |a i| ^ 3
  let S₄ := ∑ i ∈ t, w i * (a i) ^ 4
  have hS₁ : 0 ≤ S₁ := sum_nonneg fun i hi => mul_nonneg (hw i hi) (abs_nonneg _)
  have hS₂ : 0 ≤ S₂ := sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hS₃ : 0 ≤ S₃ := sum_nonneg fun i hi =>
    mul_nonneg (hw i hi) (pow_nonneg (abs_nonneg _) _)
  have hS₄ : 0 ≤ S₄ := sum_nonneg fun i hi =>
    mul_nonneg (hw i hi) (by positivity)
  have h12 : S₂ ^ 2 ≤ S₁ * S₃ := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul t
      (fun i hi => mul_nonneg (hw i hi) (abs_nonneg _))
      (fun i hi => mul_nonneg (hw i hi) (pow_nonneg (abs_nonneg _) _))
    intro i _hi
    apply le_of_eq
    calc
      (w i * (a i) ^ 2) ^ 2 = (w i) ^ 2 * ((a i) ^ 2) ^ 2 := by ring
      _ = (w i) ^ 2 * (|a i| ^ 2) ^ 2 := by rw [sq_abs]
      _ = (w i * |a i|) * (w i * |a i| ^ 3) := by ring
  have h34 : S₃ ^ 2 ≤ S₂ * S₄ := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul t
      (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
      (fun i hi => mul_nonneg (hw i hi) (show 0 ≤ (a i) ^ 4 by positivity))
    intro i _hi
    apply le_of_eq
    calc
      (w i * |a i| ^ 3) ^ 2 = (w i) ^ 2 * (|a i| ^ 2) ^ 3 := by ring
      _ = (w i) ^ 2 * ((a i) ^ 2) ^ 3 := by rw [sq_abs]
      _ = (w i * (a i) ^ 2) * (w i * (a i) ^ 4) := by ring
  change S₂ ^ 3 ≤ S₁ ^ 2 * S₄
  by_cases hzero : S₂ = 0
  · rw [hzero]
    simpa using mul_nonneg (sq_nonneg S₁) hS₄
  · have hpos : 0 < S₂ := lt_of_le_of_ne hS₂ (Ne.symm hzero)
    have hsquare := mul_self_le_mul_self (sq_nonneg S₂) h12
    have hmul := mul_le_mul_of_nonneg_left h34 (sq_nonneg S₁)
    have hfinal : S₂ * S₂ ^ 3 ≤ S₂ * (S₁ ^ 2 * S₄) := by nlinarith
    exact le_of_mul_le_mul_left hfinal hpos

end

end Erdos1122
