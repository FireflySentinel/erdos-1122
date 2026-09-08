import Erdos1122.StrongAdditive
import Erdos1122.Clipping
import Mathlib.Data.Nat.Factorization.Induction

/-! # Exact prime-power expansion of an additive function -/

namespace Erdos1122

open Finset Real
open Statements

set_option autoImplicit false

noncomputable section

theorem Statements.IsAdditive.map_one {f : ℕ → ℝ} (hf : IsAdditive f) : f 1 = 0 := by
  have hh := hf 1 1 (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.one_mul] at hh
  linarith

/-- The exponent is the exact valuation: every prime power here satisfies
`p ^ n.factorization p ∥ n`. -/
theorem Statements.IsAdditive.factorization_sum {f : ℕ → ℝ} (hf : IsAdditive f) :
    ∀ n : ℕ, 0 < n → f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p k hp hk _
    simp [Nat.primeFactors_prime_pow hk.ne' hp, hp.factorization_pow]
  · intro hn
    omega
  · intro _
    simp [hf.map_one]
  · intro a b ha hb hab ih₁ ih₂ _
    rw [hf a b (by omega) (by omega) hab, ih₁ (by omega), ih₂ (by omega),
      hab.primeFactors_mul, sum_union hab.disjoint_primeFactors]
    congr 1
    · apply sum_congr rfl
      intro p hp
      have hz : b.factorization p = 0 := Finsupp.notMem_support_iff.1
        (show p ∉ b.primeFactors from fun hpb => disjoint_left.1 hab.disjoint_primeFactors hp hpb)
      rw [Nat.factorization_mul_of_coprime hab, Finsupp.add_apply, hz, add_zero]
    · apply sum_congr rfl
      intro p hp
      have hz : a.factorization p = 0 := Finsupp.notMem_support_iff.1
        (show p ∉ a.primeFactors from fun hpa => disjoint_left.1 hab.disjoint_primeFactors hpa hp)
      rw [Nat.factorization_mul_of_coprime hab, Finsupp.add_apply, hz, zero_add]

theorem log_factorization_sum (n : ℕ) (hn : 0 < n) :
    log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * log p := by
  have hl : IsAdditive (fun n : ℕ => log (n : ℝ)) := by
    intro a b ha hb _
    change log ((a * b : ℕ) : ℝ) = log (a : ℝ) + log (b : ℝ)
    rw [Nat.cast_mul, log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
  rw [hl.factorization_sum n hn]
  apply sum_congr rfl
  intro p _
  rw [Nat.cast_pow, log_pow]

/-- Exact difference of the two arguments before clipping. The terms with
valuation one vanish, so only higher prime powers remain. -/
theorem additive_higher_prime_power_identity (f : ℕ → ℝ) (hf : IsAdditive f)
    (n : ℕ) (hn : 0 < n) (s c : ℝ) :
    (f n / s - c * log n) - (∑ p ∈ n.primeFactors, (f p / s - c * log p)) =
      ∑ p ∈ n.primeFactors with 2 ≤ n.factorization p,
        ((f (p ^ n.factorization p) - f p) / s -
          c * ((n.factorization p : ℝ) - 1) * log p) := by
  rw [hf.factorization_sum n hn, log_factorization_sum n hn, sum_div, mul_sum,
    ← sum_sub_distrib, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hk : 2 ≤ n.factorization p
  · simp only [if_pos hk]
    ring
  · have hpos : 0 < n.factorization p := by
      have hmem : p ∈ n.factorization.support := hp
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hmem)
    have he : n.factorization p = 1 := by omega
    simp [he]

/-- The clipped discrepancy is bounded by that exact higher-power sum. -/
theorem clipped_higher_prime_power_bound (f : ℕ → ℝ) (hf : IsAdditive f)
    (n : ℕ) (hn : 0 < n) (K s c a : ℝ) :
    |clip K (f n / s - c * log n - a) -
      clip K ((∑ p ∈ n.primeFactors, (f p / s - c * log p)) - a)| ≤
      |∑ p ∈ n.primeFactors with 2 ≤ n.factorization p,
        ((f (p ^ n.factorization p) - f p) / s -
          c * ((n.factorization p : ℝ) - 1) * log p)| := by
  have hh := clip_lipschitz K (f n / s - c * log n - a)
    ((∑ p ∈ n.primeFactors, (f p / s - c * log p)) - a)
  simpa only [sub_sub_sub_cancel_right, additive_higher_prime_power_identity f hf n hn s c] using hh

end

end Erdos1122
