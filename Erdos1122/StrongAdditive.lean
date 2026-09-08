import Erdos1122.Statements
import Erdos1122.FiniteCounting
import Mathlib.Analysis.PSeries

/-! # Strongly additive functions and their prime-power moments -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

/-- A strongly additive function is the sum of its values at the distinct
prime divisors. Its value at zero is not constrained. -/
def IsStronglyAdditive (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → f n = ∑ p ∈ n.primeFactors, f p

theorem IsStronglyAdditive.isAdditive {f : ℕ → ℝ} (hf : IsStronglyAdditive f) :
    IsAdditive f := by
  intro a b ha hb hab
  rw [hf (a * b) (Nat.mul_pos ha hb), hab.primeFactors_mul,
    sum_union hab.disjoint_primeFactors, ← hf a ha, ← hf b hb]

theorem IsStronglyAdditive.prime_pow {f : ℕ → ℝ} (hf : IsStronglyAdditive f)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : f (p ^ k) = f p := by
  rw [hf (p ^ k) (pow_pos hp.pos k), Nat.primeFactors_prime_pow hk.ne' hp]
  simp

def primeCenter (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊X⌋₊, f p / (p : ℝ)

def primeMoment (f : ℕ → ℝ) (X : ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ^ j / (p : ℝ)

theorem IsStronglyAdditive.eq_divisorSum {f : ℕ → ℝ} (hf : IsStronglyAdditive f)
    (X : ℝ) (n : ℕ) (hn : 0 < n) (hnX : n ≤ ⌊X⌋₊) :
    f n = divisorSum (Nat.primesLE ⌊X⌋₊) f n := by
  rw [hf n hn, divisorSum, ← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hd, _⟩
    exact ⟨⟨(Nat.le_of_dvd hn hd).trans hnX, hp⟩, hd⟩
  · rintro ⟨⟨_, hp⟩, hd⟩
    exact ⟨hp, hd, hn.ne'⟩

theorem IsStronglyAdditive.dyadic_center_identity {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) (Y : ℝ) :
    dyadicMean f Y - primeCenter f Y =
      ∑ p ∈ Nat.primesLE ⌊Y⌋₊, f p * ((2 / Y) *
        ((⌊Y / (p : ℝ)⌋₊ : ℝ) - (⌊Y / (2 * (p : ℝ))⌋₊ : ℝ)) - 1 / (p : ℝ)) := by
  rw [← dyadic_divisor_center_identity_real]
  unfold dyadicMean primeCenter
  congr 2
  apply sum_congr rfl
  intro n hn
  exact hf.eq_divisorSum Y n (by have := (mem_Ioc.1 hn).1; omega) (mem_Ioc.1 hn).2

/-- A finite geometric tail; the lower exponent is arbitrary. -/
theorem reciprocal_prime_power_sum_le (p r N : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Icc r N, 1 / (p : ℝ) ^ k) ≤ 2 / (p : ℝ) ^ r := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hhalf : 1 / (p : ℝ) ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  calc
    _ = (1 / (p : ℝ) ^ r) * ∑ k ∈ range (N + 1 - r), (1 / (p : ℝ)) ^ k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      simp [pow_add, div_eq_mul_inv, mul_comm]
    _ ≤ (1 / (p : ℝ) ^ r) * ∑ k ∈ range (N + 1 - r), (1 / 2 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun k _ => pow_le_pow_left₀ (by positivity) hhalf k
    _ ≤ (1 / (p : ℝ) ^ r) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = _ := by ring

theorem IsStronglyAdditive.primePowerMoment_le {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) (X : ℝ) (j : ℕ) :
    primePowerMoment f X j ≤ 2 * primeMoment f X j := by
  unfold primePowerMoment primePowerIndices
  calc
    _ ≤ ∑ q ∈ (Nat.primesLE ⌊X⌋₊).product (Icc 1 ⌊X⌋₊),
        |f (q.1 ^ q.2)| ^ j / ((q.1 ^ q.2 : ℕ) : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro _ _ _
      positivity
    _ = ∑ p ∈ Nat.primesLE ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
        |f (p ^ k)| ^ j / ((p ^ k : ℕ) : ℝ) := sum_product _ _ _
    _ = ∑ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ^ j * ∑ k ∈ Icc 1 ⌊X⌋₊, 1 / (p : ℝ) ^ k := by
      apply sum_congr rfl
      intro p hp
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [hf.prime_pow (Nat.prime_of_mem_primesLE hp) (mem_Icc.1 hk).1, Nat.cast_pow]
      ring
    _ ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ^ j * (2 / (p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using reciprocal_prime_power_sum_le p 1 ⌊X⌋₊ (Nat.prime_of_mem_primesLE hp).two_le
    _ = _ := by unfold primeMoment; rw [mul_sum]; apply sum_congr rfl; intro p _; ring

end

end Erdos1122
