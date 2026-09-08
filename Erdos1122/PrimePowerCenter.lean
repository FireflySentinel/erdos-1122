import Erdos1122.CenterErrors

/-! # Elliott's center and the prime center -/

namespace Erdos1122

open Finset Real
open Statements

noncomputable section

def primePowerKernel (p : ℕ) (X : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊X⌋₊, if ((p ^ k : ℕ) : ℝ) ≤ X then 1 / (p : ℝ) ^ k else 0

theorem IsStronglyAdditive.unweightedCenter_eq {f : ℕ → ℝ} (hf : IsStronglyAdditive f) (X : ℝ) :
    unweightedCenter f X = ∑ p ∈ Nat.primesLE ⌊X⌋₊, f p * primePowerKernel p X := by
  unfold unweightedCenter primePowerIndices
  rw [sum_filter]
  calc
    _ = ∑ p ∈ Nat.primesLE ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
        if ((p ^ k : ℕ) : ℝ) ≤ X then f (p ^ k) / ((p ^ k : ℕ) : ℝ) else 0 := sum_product _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      unfold primePowerKernel
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [hf.prime_pow (Nat.prime_of_mem_primesLE hp) (mem_Icc.1 hk).1]
      split_ifs <;> simp [Nat.cast_pow, div_eq_mul_inv]

theorem primePowerKernel_sub (p : ℕ) (X : ℝ) (hX : 2 ≤ X) (hp : p ∈ Nat.primesLE ⌊X⌋₊) :
    primePowerKernel p X - 1 / (p : ℝ) =
      ∑ k ∈ Icc 2 ⌊X⌋₊, if ((p ^ k : ℕ) : ℝ) ≤ X then 1 / (p : ℝ) ^ k else 0 := by
  have hN : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by norm_num; linarith)
  have he : Icc 1 ⌊X⌋₊ = {1} ∪ Icc 2 ⌊X⌋₊ := by
    ext k
    simp only [mem_union, mem_singleton, mem_Icc]
    omega
  have hd : Disjoint ({1} : Finset ℕ) (Icc 2 ⌊X⌋₊) := by simp
  have hpX : (p : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).1 (Nat.mem_primesLE.1 hp).1
  unfold primePowerKernel
  rw [he, sum_union hd]
  simp [hpX]

theorem primePowerKernel_error (p : ℕ) (X : ℝ) (hX : 2 ≤ X) (hp : p ∈ Nat.primesLE ⌊X⌋₊) :
    0 ≤ primePowerKernel p X - 1 / (p : ℝ) ∧
      primePowerKernel p X - 1 / (p : ℝ) ≤ 2 / (p : ℝ) ^ 2 := by
  rw [primePowerKernel_sub p X hX hp]
  constructor
  · exact sum_nonneg fun k _ => by split_ifs <;> positivity
  · apply le_trans _ (reciprocal_prime_power_sum_le p 2 ⌊X⌋₊ (Nat.prime_of_mem_primesLE hp).two_le)
    exact sum_le_sum fun k _ => by split_ifs; exact le_rfl; positivity

theorem prime_inverse_square_sum_le (X : ℝ) (hX : 2 ≤ X) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hN : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by norm_num; linarith)
  calc
    _ ≤ ∑ n ∈ Ioc 1 ⌊X⌋₊, ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact mem_Ioc.2 ⟨(Nat.prime_of_mem_primesLE hp).one_lt, (Nat.mem_primesLE.1 hp).1⟩
      · intro _ _ _
        positivity
    _ ≤ (1 : ℝ)⁻¹ - (⌊X⌋₊ : ℝ)⁻¹ := by
      simpa using (sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (1 : ℕ) ≠ 0) hN)
    _ ≤ 1 := by simp

theorem IsStronglyAdditive.unweighted_center_error_le {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) (X L : ℝ) (hX : 2 ≤ X) (hL : 0 ≤ L)
    (hcoeff : ∀ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ≤ L) :
    |unweightedCenter f X - primeCenter f X| ≤ 2 * L := by
  rw [hf.unweightedCenter_eq]
  unfold primeCenter
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, |f p * primePowerKernel p X - f p / (p : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, L * (2 / (p : ℝ) ^ 2) := by
      apply sum_le_sum
      intro p hp
      have he : f p * primePowerKernel p X - f p / (p : ℝ) =
          f p * (primePowerKernel p X - 1 / (p : ℝ)) := by ring
      rw [he, abs_mul, abs_of_nonneg (primePowerKernel_error p X hX hp).1]
      exact mul_le_mul (hcoeff p hp) (primePowerKernel_error p X hX hp).2
        (primePowerKernel_error p X hX hp).1 hL
    _ = (2 * L) * ∑ p ∈ Nat.primesLE ⌊X⌋₊, 1 / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ (2 * L) * 1 := mul_le_mul_of_nonneg_left (prime_inverse_square_sum_le X hX) (by positivity)
    _ = _ := mul_one _

theorem two_term_fourth_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h₂ : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h₄ : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have hh := mul_self_le_mul_self (sq_nonneg (a + b)) h₂
  nlinarith

theorem primeMoment_fourth_le (f : ℕ → ℝ) (X L : ℝ)
    (hcoeff : ∀ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ≤ L) :
    primeMoment f X 4 ≤ L ^ 2 * primeMoment f X 2 := by
  unfold primeMoment
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hcoeff p hp) 2)
    (sq_nonneg |f p|)
  nlinarith only [hh]

theorem abs_pow_four (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  simp only [show 4 = 2 * 2 from rfl, pow_mul, sq_abs]

/-- A uniform fourth moment at the prime center, derived from Elliott's
original statement with its different center. -/
theorem stronglyAdditive_fourth_moment_of_elliott (hE : Elliott) (L V : ℝ) (hL : 0 ≤ L) (hV : 0 ≤ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ X : ℝ, 2 ≤ X →
      (∀ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ≤ L) → primeMoment f X 2 ≤ V →
      initialMean (fun n => (f n - primeCenter f X) ^ 4) X ≤ C := by
  obtain ⟨E, hEpos, hE⟩ := hE
  refine ⟨8 * (E * ((2 * V) ^ 2 + 2 * L ^ 2 * V) + (2 * L) ^ 4), by positivity, ?_⟩
  intro f hf X hX hcoeff hmass
  have hb₂ := (hf.primePowerMoment_le X 2).trans (mul_le_mul_of_nonneg_left hmass (by norm_num))
  have hb₄ := (hf.primePowerMoment_le X 4).trans
    (mul_le_mul_of_nonneg_left ((primeMoment_fourth_le f X L hcoeff).trans
      (mul_le_mul_of_nonneg_left hmass (sq_nonneg L))) (by norm_num))
  have hEbound := hE f hf.isAdditive X hX
  have hb₂n : 0 ≤ primePowerMoment f X 2 := by unfold primePowerMoment; positivity
  have hpow := pow_le_pow_left₀ hb₂n hb₂ 2
  have hEm := mul_le_mul_of_nonneg_left (add_le_add hpow hb₄) hEpos.le
  have hcenter := hf.unweighted_center_error_le X L hX hL hcoeff
  have hcentpow : (unweightedCenter f X - primeCenter f X) ^ 4 ≤ (2 * L) ^ 4 := by
    simpa only [abs_pow_four] using pow_le_pow_left₀ (abs_nonneg _) hcenter 4
  have hX0 : 0 < X := by linarith
  unfold initialMean at hEbound ⊢
  have hsum : (∑ n ∈ Ioc 0 ⌊X⌋₊, (f n - primeCenter f X) ^ 4) ≤
      8 * (∑ n ∈ Ioc 0 ⌊X⌋₊, |f n - unweightedCenter f X| ^ 4) +
        8 * X * (2 * L) ^ 4 := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 ⌊X⌋₊, 8 * (|f n - unweightedCenter f X| ^ 4 + (2 * L) ^ 4) := by
        apply sum_le_sum
        intro n _
        have hh := two_term_fourth_le (f n - unweightedCenter f X)
          (unweightedCenter f X - primeCenter f X)
        simp only [sub_add_sub_cancel] at hh
        rw [abs_pow_four]
        linarith
      _ ≤ _ := by
        simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
        nlinarith [mul_le_mul_of_nonneg_right (Nat.floor_le hX0.le) (show 0 ≤ (2 * L) ^ 4 by positivity)]
  have hEfinal : (∑ n ∈ Ioc 0 ⌊X⌋₊, |f n - unweightedCenter f X| ^ 4) / X ≤
      E * ((2 * V) ^ 2 + 2 * L ^ 2 * V) := by nlinarith only [hEbound, hEm]
  apply (div_le_iff₀ hX0).2
  have hm := (div_le_iff₀ hX0).1 hEfinal
  nlinarith only [hsum, hm]

end

end Erdos1122
