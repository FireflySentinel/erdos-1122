import Erdos1122.PrimePowers
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Exact finite counts in (2.7) and (5.4) -/

namespace Erdos1122

open Finset

noncomputable section

def divisorSum (P : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ n then a p else 0

theorem divisorSum_initial_sum (P : Finset ℕ) (a : ℕ → ℝ) (Y : ℕ) :
    (∑ n ∈ Ioc 0 Y, divisorSum P a n) = ∑ p ∈ P, a p * (Y / p : ℕ) := by
  unfold divisorSum
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

theorem divisorSum_dyadic_sum (P : Finset ℕ) (a : ℕ → ℝ) (Y : ℕ) :
    (∑ n ∈ Ioc (Y / 2) Y, divisorSum P a n) =
      ∑ p ∈ P, a p * ((Y / p : ℕ) - ((Y / (2 * p) : ℕ) : ℝ)) := by
  have hsplit : (∑ n ∈ Ioc 0 Y, divisorSum P a n) =
      (∑ n ∈ Ioc 0 (Y / 2), divisorSum P a n) +
      ∑ n ∈ Ioc (Y / 2) Y, divisorSum P a n := by
    have he : Ioc 0 Y = Ioc 0 (Y / 2) ∪ Ioc (Y / 2) Y := by
      ext n
      simp only [mem_union, mem_Ioc]
      have := Nat.div_le_self Y 2
      omega
    have hd : Disjoint (Ioc 0 (Y / 2)) (Ioc (Y / 2) Y) := by
      apply disjoint_left.2
      intro n hn hm
      simp only [mem_Ioc] at hn hm
      omega
    rw [he, sum_union hd]
  rw [divisorSum_initial_sum, divisorSum_initial_sum] at hsplit
  rw [← sub_eq_iff_eq_add'] at hsplit
  rw [← hsplit, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [Nat.div_div_eq_div_mul]
  ring

/-- An exact identity, including both floor errors. There is no asymptotic
estimate or bound on the coefficients in this statement. -/
theorem dyadic_divisor_center_identity (P : Finset ℕ) (a : ℕ → ℝ) (Y : ℕ) :
    (2 / (Y : ℝ)) * (∑ n ∈ Ioc (Y / 2) Y, divisorSum P a n) -
        (∑ p ∈ P, a p / (p : ℝ)) =
      ∑ p ∈ P, a p * ((2 / (Y : ℝ)) *
        ((Y / p : ℕ) - ((Y / (2 * p) : ℕ) : ℝ)) - 1 / (p : ℝ)) := by
  rw [divisorSum_dyadic_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  ring

/-- Equation (2.7), with a real cutoff and the manuscript's normalization.
Taking `P` to be the primes at most `Y` gives its strongly additive form. -/
theorem dyadic_divisor_center_identity_real (P : Finset ℕ) (a : ℕ → ℝ) (Y : ℝ) :
    (2 / Y) * (∑ n ∈ Ioc ⌊Y / 2⌋₊ ⌊Y⌋₊, divisorSum P a n) -
        (∑ p ∈ P, a p / (p : ℝ)) =
      ∑ p ∈ P, a p * ((2 / Y) *
        ((⌊Y / (p : ℝ)⌋₊ : ℝ) - (⌊Y / (2 * (p : ℝ))⌋₊ : ℝ)) - 1 / (p : ℝ)) := by
  rw [Nat.floor_div_ofNat, divisorSum_dyadic_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [show 2 * (p : ℝ) = ((2 * p : ℕ) : ℝ) by norm_cast]
  simp only [Nat.floor_div_natCast]
  ring

def primeDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ := #{p ∈ P | p ∣ n}

theorem primeDivisorCount_eq_sum (P : Finset ℕ) (n : ℕ) :
    (primeDivisorCount P n : ℝ) = ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0 := by
  simp [primeDivisorCount]

theorem prime_divisor_indicator_le (P : Finset ℕ) (n : ℕ) :
    (if 1 ≤ primeDivisorCount P n then (1 : ℝ) else 0) ≤
      ∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0 := by
  rw [← primeDivisorCount_eq_sum]
  split_ifs with h
  · exact_mod_cast h
  · positivity

theorem primeDivisorCount_factorial (P : Finset ℕ) (n : ℕ) :
    (primeDivisorCount P n : ℝ) * ((primeDivisorCount P n : ℝ) - 1) =
      ∑ q ∈ P.offDiag, if q.1 ∣ n ∧ q.2 ∣ n then (1 : ℝ) else 0 := by
  have he : P.offDiag.filter (fun q => q.1 ∣ n ∧ q.2 ∣ n) =
      (P.filter (fun p => p ∣ n)).offDiag := by
    ext q
    simp only [mem_filter, mem_offDiag]
    tauto
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, he, offDiag_card]
  have hc : (P.filter (fun p => p ∣ n)).card ≤
      (P.filter (fun p => p ∣ n)).card * (P.filter (fun p => p ∣ n)).card := by
    exact Nat.le_mul_self _
  rw [Nat.cast_sub hc, Nat.cast_mul]
  unfold primeDivisorCount
  ring

/-- The second factorial moment uses distinct primes, hence counts multiples
of their product. No independence assumption is made. -/
theorem prime_divisor_factorial_moment (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X : ℕ) :
    (∑ n ∈ Ioc 0 X,
      (primeDivisorCount P n : ℝ) * ((primeDivisorCount P n : ℝ) - 1)) ≤
      (X : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 := by
  simp_rw [primeDivisorCount_factorial]
  rw [sum_comm]
  calc
    _ ≤ ∑ q ∈ P.offDiag, (X : ℝ) * (1 / (q.1 : ℝ) * (1 / (q.2 : ℝ))) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hp, hq', hne⟩ := mem_offDiag.1 hq
      have hcop := (Nat.coprime_primes (hP _ hp) (hP _ hq')).2 hne
      have hd (n : ℕ) : q.1 ∣ n ∧ q.2 ∣ n ↔ q.1 * q.2 ∣ n := by
        constructor
        · rintro ⟨h₁, h₂⟩
          exact hcop.mul_dvd_of_dvd_of_dvd h₁ h₂
        · intro h
          exact ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩
      simp_rw [hd]
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.Ioc_filter_dvd_card_eq_div]
      calc
        ((X / (q.1 * q.2) : ℕ) : ℝ) ≤ (X : ℝ) / ((q.1 * q.2 : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = _ := by simp [Nat.cast_mul, div_eq_mul_inv, mul_comm]
    _ = (X : ℝ) * ∑ q ∈ P.offDiag, 1 / (q.1 : ℝ) * (1 / (q.2 : ℝ)) := by
      rw [mul_sum]
    _ ≤ (X : ℝ) * ∑ q ∈ P.product P, 1 / (q.1 : ℝ) * (1 / (q.2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact mem_product.2 ⟨(mem_offDiag.1 hq).1, (mem_offDiag.1 hq).2.1⟩
      · intro _ _ _
        positivity
    _ = _ := by
      congr 1
      calc
        _ = ∑ p ∈ P, ∑ q ∈ P, 1 / (p : ℝ) * (1 / (q : ℝ)) :=
          sum_product P P (fun q : ℕ × ℕ => 1 / (q.1 : ℝ) * (1 / (q.2 : ℝ)))
        _ = _ := by rw [← sum_mul_sum, pow_two]

theorem prime_divisor_factorial_mean_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X : ℕ) (hX : 0 < X) (M : ℝ)
    (hmass : (∑ p ∈ P, 1 / (p : ℝ)) ≤ M) :
    (∑ n ∈ Ioc 0 X,
      (primeDivisorCount P n : ℝ) * ((primeDivisorCount P n : ℝ) - 1)) / (X : ℝ) ≤ M ^ 2 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  apply (div_le_iff₀ hXr).2
  apply (prime_divisor_factorial_moment P hP X).trans
  rw [mul_comm (M ^ 2)]
  apply mul_le_mul_of_nonneg_left _ hXr.le
  exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hmass 2

theorem prime_divisor_factorial_mean_le_real (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (X M : ℝ) (hX : 0 < X) (hmass : (∑ p ∈ P, 1 / (p : ℝ)) ≤ M) :
    (∑ n ∈ Ioc 0 ⌊X⌋₊,
      (primeDivisorCount P n : ℝ) * ((primeDivisorCount P n : ℝ) - 1)) / X ≤ M ^ 2 := by
  apply (div_le_iff₀ hX).2
  calc
    _ ≤ (⌊X⌋₊ : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 :=
      prime_divisor_factorial_moment P hP ⌊X⌋₊
    _ ≤ X * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right (Nat.floor_le hX.le) (sq_nonneg _)
    _ ≤ X * M ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hmass 2) hX.le
    _ = _ := mul_comm _ _

end

end Erdos1122
