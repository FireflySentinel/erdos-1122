import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-! # The higher-prime-power exceptional set -/

namespace Erdos1122

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem summable_shifted_power_reciprocals :
    Summable (fun q : ℕ × ℕ => 1 / ((q.1 + 2 : ℕ) : ℝ) ^ (q.2 + 2)) := by
  have hp : Summable (fun p : ℕ => 1 / ((p + 2 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 2).2 (Real.summable_one_div_nat_pow.2 (by decide : 1 < 2))
  have hg : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply (hp.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)).of_nonneg_of_le
    (fun _ => by positivity)
  intro q
  have hbase : 1 / ((q.1 + 2 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast (show 2 ≤ q.1 + 2 by omega)
  calc
    _ = (1 / ((q.1 + 2 : ℕ) : ℝ) ^ 2) *
        (1 / ((q.1 + 2 : ℕ) : ℝ)) ^ q.2 := by rw [one_div_pow]; simp [pow_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase q.2)
      (by positivity)

/-- Absolute convergence of all the higher-prime-power reciprocals, including after
removing any finite set. This is proved, rather than imposed on the union bound. -/
theorem summable_higher_prime_powers (F : Finset (ℕ × ℕ)) :
    Summable (fun q : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F} =>
      1 / ((q.val.1 : ℝ) ^ q.val.2)) := by
  let shift : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F} → ℕ × ℕ :=
    fun q => (q.val.1 - 2, q.val.2 - 2)
  have hinj : Function.Injective shift := by
    intro q r h
    apply Subtype.ext
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    have hq := q.property.1.two_le
    have hr := r.property.1.two_le
    have hqk := q.property.2.1
    have hrk := r.property.2.1
    dsimp [shift] at h₁ h₂
    apply Prod.ext <;> omega
  convert! summable_shifted_power_reciprocals.comp_injective hinj using 1
  ext q
  simp only [Function.comp_apply, shift,
    Nat.sub_add_cancel q.property.1.two_le, Nat.sub_add_cancel q.property.2.1]

/-- The union bound for any finite indexed family of divisors.
Repeated divisors are permitted. -/
theorem finite_divisor_union_bound {ι : Type*} (s : Finset ι) (d : ι → ℕ) (X : ℕ) :
    (#{n ∈ Ioc 0 X | ∃ i ∈ s, d i ∣ n} : ℝ) ≤
      (X : ℝ) * ∑ i ∈ s, 1 / (d i : ℝ) := by
  classical
  have heq : {n ∈ Ioc 0 X | ∃ i ∈ s, d i ∣ n} =
      s.biUnion (fun i => {n ∈ Ioc 0 X | d i ∣ n}) := by
    ext n
    simp only [mem_filter, mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ((∑ i ∈ s, #{n ∈ Ioc 0 X | d i ∣ n} : ℕ) : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ = ∑ i ∈ s, ((X / d i : ℕ) : ℝ) := by
      simp only [Nat.cast_sum, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ i ∈ s, (X : ℝ) / (d i : ℝ) := sum_le_sum fun _ _ => Nat.cast_div_le
    _ = _ := by simp [mul_sum, div_eq_mul_inv]

/-- A countable (indeed arbitrarily indexed) union bound. Summability is an explicit
hypothesis, so the real-valued infinite sum cannot silently default to zero. -/
theorem divisor_union_bound {ι : Type*} (d : ι → ℕ) (X : ℕ)
    (hs : Summable (fun i => 1 / (d i : ℝ))) :
    (#{n ∈ Ioc 0 X | ∃ i, d i ∣ n} : ℝ) ≤
      (X : ℝ) * ∑' i, 1 / (d i : ℝ) := by
  classical
  let bad := {n ∈ Ioc 0 X | ∃ i, d i ∣ n}
  have hex (n : bad) : ∃ i, d i ∣ (n : ℕ) := (mem_filter.mp n.property).2
  let chooseDivisor : bad → ι := fun n => (hex n).choose
  let s : Finset ι := bad.attach.image chooseDivisor
  have hsub : bad ⊆ {n ∈ Ioc 0 X | ∃ i ∈ s, d i ∣ n} := by
    intro n hn
    refine mem_filter.mpr ⟨(mem_filter.mp hn).1, ?_⟩
    refine ⟨chooseDivisor ⟨n, hn⟩, ?_, (hex ⟨n, hn⟩).choose_spec⟩
    exact mem_image.mpr ⟨⟨n, hn⟩, mem_attach _ _, rfl⟩
  calc
    _ ≤ (#{n ∈ Ioc 0 X | ∃ i ∈ s, d i ∣ n} : ℝ) := by
      exact_mod_cast card_le_card hsub
    _ ≤ (X : ℝ) * ∑ i ∈ s, 1 / (d i : ℝ) := finite_divisor_union_bound s d X
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum s (fun _ _ => by positivity))
      (Nat.cast_nonneg X)

/-- Prime powers outside the finite retained set in Section 5. -/
theorem higher_prime_power_union_bound (X : ℕ) (F : Finset (ℕ × ℕ)) :
    (#{n ∈ Ioc 0 X | ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ (p, k) ∉ F ∧ p ^ k ∣ n} : ℝ)
      ≤ (X : ℝ) * ∑' q : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F},
        1 / ((q.val.1 : ℝ) ^ q.val.2) := by
  classical
  have h := divisor_union_bound
    (fun q : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F} => q.val.1 ^ q.val.2) X
    (by simpa only [Nat.cast_pow] using summable_higher_prime_powers F)
  simpa only [Nat.cast_pow, Subtype.exists, Prod.exists, exists_prop, and_assoc] using h

end

end Erdos1122
