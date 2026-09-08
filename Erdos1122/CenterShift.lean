import Erdos1122.PrimePowerCenter

/-! # Changing between weighted and unweighted centers -/

namespace Erdos1122

open Finset Real
open Statements

noncomputable section

def centerShiftKernel (X : ℝ) : ℝ :=
  ∑ q ∈ primePowerIndices X, 1 / (q.1 : ℝ) ^ (q.2 + 2)

theorem center_shift_identity (f : ℕ → ℝ) (X : ℝ) :
    weightedCenter f X - unweightedCenter f X =
      -(∑ q ∈ primePowerIndices X, f (q.1 ^ q.2) / ((q.1 : ℝ) ^ q.2 * q.1)) := by
  unfold weightedCenter unweightedCenter
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  apply sum_congr rfl
  intro q _
  rw [Nat.cast_pow]
  ring

/-- Cauchy--Schwarz with the exact prime-power kernel; no additivity is needed. -/
theorem center_shift (f : ℕ → ℝ) (X : ℝ) :
    |weightedCenter f X - unweightedCenter f X| ≤
      sqrt (centerShiftKernel X) * sqrt (primePowerMoment f X 2) := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (primePowerIndices X)
    (f := fun q => 1 / (q.1 : ℝ) ^ (q.2 + 2))
    (g := fun q => |f (q.1 ^ q.2)| ^ 2 / ((q.1 ^ q.2 : ℕ) : ℝ))
    (r := fun q => f (q.1 ^ q.2) / ((q.1 : ℝ) ^ q.2 * q.1))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun q hq => by
      have hp := (Nat.mem_primesLE.1 (mem_product.1 (mem_filter.1 hq).1).1).2
      have hp0 : (q.1 : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [Nat.cast_pow, sq_abs, pow_add]
      apply le_of_eq
      field_simp)
  rw [center_shift_identity, abs_neg]
  have hn : 0 ≤ centerShiftKernel X := by unfold centerShiftKernel; positivity
  rw [← sqrt_mul hn]
  apply le_sqrt_of_sq_le
  simpa only [sq_abs, centerShiftKernel, primePowerMoment] using hc


theorem centerShiftKernel_le_one (X : ℝ) (hX : 2 ≤ X) : centerShiftKernel X ≤ 1 := by
  unfold centerShiftKernel primePowerIndices
  calc
    _ ≤ ∑ q ∈ (Nat.primesLE ⌊X⌋₊).product (Icc 1 ⌊X⌋₊),
        1 / (q.1 : ℝ) ^ (q.2 + 2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = ∑ p ∈ Nat.primesLE ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊, 1 / (p : ℝ) ^ (k + 2) := sum_product _ _ _
    _ = ∑ p ∈ Nat.primesLE ⌊X⌋₊, (1 / (p : ℝ) ^ 2) *
        ∑ k ∈ Icc 1 ⌊X⌋₊, 1 / (p : ℝ) ^ k := by
      apply sum_congr rfl
      intro p _
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      simp [pow_add, div_eq_mul_inv, mul_comm]
    _ ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, 1 / (p : ℝ) ^ 2 := by
      apply sum_le_sum
      intro p hp
      have hprime := Nat.prime_of_mem_primesLE hp
      have htail := reciprocal_prime_power_sum_le p 1 ⌊X⌋₊ hprime.two_le
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hh : (∑ k ∈ Icc 1 ⌊X⌋₊, 1 / (p : ℝ) ^ k) ≤ 1 :=
        htail.trans (by simpa using (div_le_one hp0).2 hp2)
      exact mul_le_of_le_one_right (by positivity) hh
    _ ≤ 1 := prime_inverse_square_sum_le X hX

theorem center_shift_le_sqrt (f : ℕ → ℝ) (X : ℝ) (hX : 2 ≤ X) :
    |weightedCenter f X - unweightedCenter f X| ≤ sqrt (primePowerMoment f X 2) := by
  apply (center_shift f X).trans
  have hh : sqrt (centerShiftKernel X) ≤ 1 := by
    simpa using sqrt_le_sqrt (centerShiftKernel_le_one X hX)
  exact mul_le_of_le_one_left (sqrt_nonneg _) hh

theorem center_shift_sq_le (f : ℕ → ℝ) (X : ℝ) (hX : 2 ≤ X) :
    (weightedCenter f X - unweightedCenter f X) ^ 2 ≤ primePowerMoment f X 2 := by
  have hn : 0 ≤ primePowerMoment f X 2 := by unfold primePowerMoment; positivity
  simpa only [sq_abs, sq_sqrt hn] using pow_le_pow_left₀ (abs_nonneg _)
    (center_shift_le_sqrt f X hX) 2


end

end Erdos1122
