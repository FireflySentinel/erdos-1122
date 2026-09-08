import Erdos1122.PrimePowerCenter

/-! # Finite centered fourth moments

The centering operators act on monomial expectations. This keeps the
independent Bernoulli calculation separate from arithmetic floor errors.
-/

namespace Erdos1122

open Finset

set_option autoImplicit false
noncomputable section

variable {ι : Type*} [DecidableEq ι]

def centerOp (q : ι → ℝ) (i : ι) (F : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  F (insert i s) - q i * F s

def bernoulliMonomial (q : ι → ℝ) (s : Finset ι) : ℝ := ∏ i ∈ s, q i

def bernoulliCorrelation (q : ι → ℝ) (i j k l : ι) : ℝ :=
  centerOp q i (centerOp q j (centerOp q k (centerOp q l (bernoulliMonomial q)))) ∅

theorem centerOp_error (q : ι → ℝ) (i : ι) (F G : Finset ι → ℝ) (R : ℝ)
    (hq : |q i| ≤ 1) (hFG : ∀ s, |F s - G s| ≤ R) (s : Finset ι) :
    |centerOp q i F s - centerOp q i G s| ≤ 2 * R := by
  have he : centerOp q i F s - centerOp q i G s =
      (F (insert i s) - G (insert i s)) - q i * (F s - G s) := by
    unfold centerOp
    ring
  rw [he]
  calc
    _ ≤ |F (insert i s) - G (insert i s)| + |q i * (F s - G s)| := abs_sub _ _
    _ ≤ R + 1 * R := add_le_add (hFG _) (by
      rw [abs_mul]
      exact mul_le_mul hq (hFG s) (abs_nonneg _) (by norm_num))
    _ = _ := by ring

theorem four_centerOp_error (q : ι → ℝ) (i j k l : ι)
    (F G : Finset ι → ℝ) (R : ℝ) (hq : ∀ a, |q a| ≤ 1)
    (hFG : ∀ s, |F s - G s| ≤ R) :
    |centerOp q i (centerOp q j (centerOp q k (centerOp q l F))) ∅ -
      centerOp q i (centerOp q j (centerOp q k (centerOp q l G))) ∅| ≤ 16 * R := by
  have h₁ := centerOp_error q l F G R (hq l) hFG
  have h₂ := centerOp_error q k _ _ (2 * R) (hq k) h₁
  have h₃ := centerOp_error q j _ _ (2 * (2 * R)) (hq j) h₂
  have h₄ := centerOp_error q i _ _ (2 * (2 * (2 * R))) (hq i) h₃ ∅
  linarith

private theorem bernoulli_fourth_le (q : ℝ) :
    q - 4 * q ^ 2 + 6 * q ^ 3 - 3 * q ^ 4 ≤ q := by
  have h : 0 ≤ q ^ 2 * (3 * (q - 1) ^ 2 + 1) := by positivity
  nlinarith only [h]

private theorem bernoulli_pair_le (q r : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    q * r - q ^ 2 * r - q * r ^ 2 + q ^ 2 * r ^ 2 ≤ q * r := by
  have hq : 0 ≤ q * (1 - q) := mul_nonneg hq₀ (sub_nonneg.2 hq₁)
  have hq' : q * (1 - q) ≤ q := by nlinarith [sq_nonneg q]
  have hr' : r * (1 - r) ≤ r := by nlinarith [sq_nonneg r]
  have h := mul_le_mul hq' hr' (mul_nonneg hr₀ (sub_nonneg.2 hr₁)) hq₀
  nlinarith only [h]

set_option maxHeartbeats 2000000 in
/-- Only paired indices and the fourfold diagonal survive centering. -/
theorem bernoulli_fourth_term_le (q a : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (i j k l : ι) :
    a i * a j * a k * a l * bernoulliCorrelation q i j k l ≤
      (if i = j ∧ j = k ∧ k = l then a i ^ 4 * q i else 0) +
      (if i = j ∧ k = l then (a i ^ 2 * q i) * (a k ^ 2 * q k) else 0) +
      (if i = k ∧ j = l then (a i ^ 2 * q i) * (a j ^ 2 * q j) else 0) +
      (if i = l ∧ j = k then (a i ^ 2 * q i) * (a j ^ 2 * q j) else 0) := by
  have hf (x : ι) := mul_le_mul_of_nonneg_left
    (bernoulli_fourth_le (q x)) (show 0 ≤ a x ^ 4 by positivity)
  have hp (x y : ι) := mul_le_mul_of_nonneg_left
    (bernoulli_pair_le (q x) (q y) (hq x).1 (hq x).2 (hq y).1 (hq y).2)
    (show 0 ≤ a x ^ 2 * a y ^ 2 by positivity)
  by_cases h₁ : i = j <;> by_cases h₂ : i = k <;> by_cases h₃ : i = l <;>
    by_cases h₄ : j = k <;> by_cases h₅ : j = l <;> by_cases h₆ : k = l <;>
    simp_all [bernoulliCorrelation, centerOp, bernoulliMonomial, prod_insert, eq_comm] <;>
    solve
    | apply le_of_eq; ring
    | nlinarith only [hf i, hf j, hf k, hf l, hp i j, hp i k, hp i l,
        hp j k, hp j l, hp k l, sq_nonneg (a i ^ 2 * q i),
        sq_nonneg (a j ^ 2 * q j), sq_nonneg (a k ^ 2 * q k), sq_nonneg (a l ^ 2 * q l)]

theorem bernoulli_fourth_sum_le (P : Finset ι) (q a : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    (∑ i ∈ P, ∑ j ∈ P, ∑ k ∈ P, ∑ l ∈ P,
      a i * a j * a k * a l * bernoulliCorrelation q i j k l) ≤
      (∑ i ∈ P, a i ^ 4 * q i) + 3 * (∑ i ∈ P, a i ^ 2 * q i) ^ 2 := by
  calc
    _ ≤ ∑ i ∈ P, ∑ j ∈ P, ∑ k ∈ P, ∑ l ∈ P,
        ((if i = j ∧ j = k ∧ k = l then a i ^ 4 * q i else 0) +
        (if i = j ∧ k = l then (a i ^ 2 * q i) * (a k ^ 2 * q k) else 0) +
        (if i = k ∧ j = l then (a i ^ 2 * q i) * (a j ^ 2 * q j) else 0) +
        (if i = l ∧ j = k then (a i ^ 2 * q i) * (a j ^ 2 * q j) else 0)) := by
      exact sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ =>
        sum_le_sum fun l _ => bernoulli_fourth_term_le q a hq i j k l
    _ = _ := by
      simp_rw [sum_add_distrib, ite_and]
      simp [← sum_mul, ← mul_sum, sq]
      ring

omit [DecidableEq ι] in
theorem sum_fourth_expand (P : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ P, a i) ^ 4 = ∑ i ∈ P, ∑ j ∈ P, ∑ k ∈ P, ∑ l ∈ P,
      a i * a j * a k * a l := by
  simp only [← sum_mul, ← mul_sum]
  ring

end

end Erdos1122
