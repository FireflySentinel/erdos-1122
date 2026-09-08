import Erdos1122.CenterShift
import Erdos1122.ComparisonFamily
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Convergence of the moving prime-power centers -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

theorem IsStronglyAdditive.weightedCenter_eq {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) (X : ℝ) :
    weightedCenter f X = ∑ p ∈ Nat.primesLE ⌊X⌋₊,
      f p * (primePowerKernel p X * (1 - 1 / (p : ℝ))) := by
  unfold weightedCenter primePowerIndices
  rw [sum_filter]
  calc
    _ = ∑ p ∈ Nat.primesLE ⌊X⌋₊, ∑ k ∈ Icc 1 ⌊X⌋₊,
        if ((p ^ k : ℕ) : ℝ) ≤ X then f (p ^ k) / ((p ^ k : ℕ) : ℝ) * (1 - 1 / (p : ℝ)) else 0 :=
      sum_product _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      unfold primePowerKernel
      rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [hf.prime_pow (Nat.prime_of_mem_primesLE hp) (mem_Icc.1 hk).1]
      split_ifs <;> simp [Nat.cast_pow, div_eq_mul_inv, mul_comm, mul_assoc]

theorem weighted_prime_kernel_error (p : ℕ) (X : ℝ) (hX : 2 ≤ X)
    (hp : p ∈ Nat.primesLE ⌊X⌋₊) :
    |primePowerKernel p X * (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hh := primePowerKernel_error p X hX hp
  have ht : primePowerKernel p X ≤ 2 / (p : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Icc 1 ⌊X⌋₊, 1 / (p : ℝ) ^ k := by
        unfold primePowerKernel
        apply sum_le_sum
        intro k _
        split_ifs
        · exact le_rfl
        · positivity
      _ ≤ _ := by simpa using reciprocal_prime_power_sum_le p 1 ⌊X⌋₊ (Nat.prime_of_mem_primesLE hp).two_le
  have hn : 0 ≤ primePowerKernel p X := by unfold primePowerKernel; positivity
  have hkp : primePowerKernel p X / (p : ℝ) ≤ 2 / (p : ℝ) ^ 2 := by
    exact (div_le_div_of_nonneg_right ht hp0.le).trans_eq (by ring)
  have he : primePowerKernel p X * (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) =
      (primePowerKernel p X - 1 / (p : ℝ)) - primePowerKernel p X / (p : ℝ) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg hh.1, abs_of_nonneg (div_nonneg hn hp0.le)]
  exact (add_le_add hh.2 hkp).trans_eq (by ring)

/-- The weighted center approaches the prime center for a uniformly bounded
family whose value at every fixed prime tends to zero. -/
theorem weighted_prime_center_tendsto (z : ℝ → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hz : ∀ X, IsStronglyAdditive (z X))
    (hcoeff : ∀ X p, p.Prime → |z X p| ≤ K)
    (hpoint : ∀ p : ℕ, p.Prime → Tendsto (fun X => z X p) atTop (𝓝 0)) :
    Tendsto (fun X => weightedCenter (z X) X - primeCenter (z X) X) atTop (𝓝 0) := by
  let a := fun X p => if p ∈ Nat.primesLE ⌊X⌋₊ then
    z X p * (primePowerKernel p X * (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)) else 0
  have ha (X : ℝ) (hX : 2 ≤ X) (p : ℕ) : |a X p| ≤ 4 * |z X p| / (p : ℝ) ^ 2 := by
    dsimp [a]
    split_ifs with hp
    · rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (weighted_prime_kernel_error p X hX hp)
        (abs_nonneg _)).trans_eq (by ring)
    · rw [abs_zero]
      positivity
  have hab (p : ℕ) : Tendsto (fun X => a X p) atTop (𝓝 0) := by
    by_cases hp : p.Prime
    · apply squeeze_zero_norm' _ (by simpa using ((hpoint p hp).abs.const_mul 4).div_const ((p : ℝ) ^ 2))
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
      simpa only [Real.norm_eq_abs] using ha X hX p
    · have he (X : ℝ) : a X p = 0 := by
        simp [a, Nat.mem_primesLE, hp]
      simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  have hbound : ∀ᶠ X in atTop, ∀ p, ‖a X p‖ ≤ 4 * K / (p : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX p
    rw [Real.norm_eq_abs]
    by_cases hp : p.Prime
    · exact (ha X hX p).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcoeff X p hp) (by norm_num)) (sq_nonneg _))
    · simp only [a, Nat.mem_primesLE, hp, and_false, ↓reduceIte, abs_zero]
      positivity
  have hs : Summable (fun p : ℕ => 4 * K / (p : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.2 (by decide : 1 < 2)).mul_left (4 * K)
  have ht := tendsto_tsum_of_dominated_convergence hs hab hbound
  have he (X : ℝ) : (∑' p, a X p) = weightedCenter (z X) X - primeCenter (z X) X := by
    rw [tsum_eq_sum (s := Nat.primesLE ⌊X⌋₊) (fun p hp => by simp [a, hp]), (hz X).weightedCenter_eq]
    unfold primeCenter
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    dsimp [a]
    rw [if_pos hp]
    ring
  simpa only [he, tsum_zero] using ht

namespace NormalizedFamily

variable {f : ℕ → ℝ} {M : ℝ}

theorem comparison_prime_tendsto (N : NormalizedFamily f M) (K : ℝ) (hK : 0 ≤ K)
    (p : ℕ) (hp : p.Prime) : Tendsto (fun X => N.comparison K X p) atTop (𝓝 0) := by
  have hu : Tendsto (fun X => N.residual X p) atTop (𝓝 0) := by
    simpa [residual] using (N.scale_tendsto.const_div_atTop (f p)).sub (N.slope_tendsto.mul_const (log p))
  have ht : Tendsto (fun X => clip K (N.residual X p)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [abs_zero] using hu.abs)
    exact Eventually.of_forall (fun X => by
      simpa [Real.norm_eq_abs, clip_eq_self (show |(0 : ℝ)| ≤ K by simpa using hK)] using
        clip_lipschitz K (N.residual X p) 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (p : ℝ), eventually_ge_atTop (0 : ℝ)] with X hpX hX
  rw [N.comparison_prime K X p hp, if_pos (Nat.mem_primesLE.2 ⟨(Nat.le_floor_iff hX).2 hpX, hp⟩)]

theorem comparison_center_tendsto (N : NormalizedFamily f M) (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun X => weightedCenter (N.comparison K X) X - primeCenter (N.comparison K X) X)
      atTop (𝓝 0) :=
  weighted_prime_center_tendsto (N.comparison K) K hK
    (N.comparison_stronglyAdditive K) (N.comparison_coeff K hK) (N.comparison_prime_tendsto K hK)

end NormalizedFamily

end

end Erdos1122
