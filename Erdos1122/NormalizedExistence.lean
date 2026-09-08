import Erdos1122.AssemblyStatements
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! # The complete normalization family in Lemma 4.1 -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

/-- A fixed finite collection of primes with sufficiently large reciprocal
mass excludes every slope bounded away from zero. -/
theorem normalization_slopes_tendsto (f : ℕ → ℝ) (s c : ℝ → ℝ) (M : ℝ)
    (hs : Tendsto s atTop atTop)
    (hlevel : ∀ᶠ X in atTop,
      cappedQuadratic (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ))
        (fun p => f p / s X) (fun p => log p) (c X) ≤ M) :
    Tendsto c atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.2
  intro ε hε
  let b : ℝ := ε * log 2 / 2
  let d : ℝ := min (b ^ 2) 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 < d := lt_min (sq_pos_of_pos hb) zero_lt_one
  obtain ⟨U, hU⟩ : ∃ U : Finset Nat.Primes, M / d < ∑ p ∈ U, (1 : ℝ) / p := by
    by_contra h
    push Not at h
    exact Nat.Primes.not_summable_one_div
      (summable_of_sum_le (fun _ => by positivity) h)
  have hsmall : ∀ᶠ X : ℝ in atTop, ∀ p ∈ U, |f p.val / s X| < b := by
    apply (eventually_all_finset U).2
    intro p _
    have ht : Tendsto (fun X => |f p.val / s X|) atTop (𝓝 0) := by
      simpa using (hs.const_div_atTop (f p.val)).abs
    exact ht.eventually (eventually_lt_nhds hb)
  have hcut : ∀ᶠ X : ℝ in atTop, ∀ p ∈ U, p.val ∈ Nat.primesLE ⌊X⌋₊ := by
    apply (eventually_all_finset U).2
    intro p _
    filter_upwards [eventually_ge_atTop (p.val : ℝ), eventually_ge_atTop (0 : ℝ)] with X hX hX0
    exact Nat.mem_primesLE.2 ⟨(Nat.le_floor_iff hX0).2 hX, p.property⟩
  filter_upwards [hlevel, hsmall, hcut] with X hX hsX hcX
  rw [Real.dist_eq, sub_zero]
  by_contra h
  have hc : ε ≤ |c X| := le_of_not_gt h
  have hterm (p : Nat.Primes) (hp : p ∈ U) :
      d / (p.val : ℝ) ≤ min ((f p.val / s X - c X * log p.val) ^ 2) 1 / (p.val : ℝ) := by
    have hlog : log 2 ≤ log p.val := log_le_log (by norm_num)
      (by exact_mod_cast p.property.two_le)
    have hlog0 : 0 ≤ log p.val := (log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hlog
    have hh := mul_le_mul hc hlog (by positivity : 0 ≤ log (2 : ℝ)) (abs_nonneg _)
    have ht := abs_sub (f p.val / s X) (f p.val / s X - c X * log p.val)
    have hab : |c X * log p.val| = |c X| * log p.val := by rw [abs_mul, abs_of_nonneg hlog0]
    have heq : f p.val / s X - (f p.val / s X - c X * log p.val) = c X * log p.val := by ring
    rw [heq, hab] at ht
    have hu : b ≤ |f p.val / s X - c X * log p.val| := by
      have := hsX p hp
      dsimp [b] at *
      linarith
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact min_le_min (by nlinarith [sq_abs (f p.val / s X - c X * log p.val)]) le_rfl
  have hmass : (∑ p ∈ U, min ((f p.val / s X - c X * log p.val) ^ 2) 1 / (p.val : ℝ)) ≤ M := by
    have hin : U.image (fun p => p.val) ⊆ Nat.primesLE ⌊X⌋₊ := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
      exact hcX q hq
    have hh := sum_le_sum_of_subset_of_nonneg hin (f := fun p : ℕ =>
      min ((f p / s X - c X * log p) ^ 2) 1 / (p : ℝ))
      (fun _ _ _ => div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity))
    rw [sum_image (g := fun p : Nat.Primes => p.val)
      (fun _ _ _ _ h => Nat.Primes.coe_nat_injective h)] at hh
    dsimp only [cappedQuadratic] at hX
    simp only [div_eq_mul_inv, mul_comm, mul_one] at hX hh ⊢
    linarith [sq_nonneg (c X)]
  have hlo := (sum_le_sum hterm).trans hmass
  have heq : (∑ p ∈ U, d / (p.val : ℝ)) = d * ∑ p ∈ U, (1 : ℝ) / p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [heq] at hlo
  have hstrict := (div_lt_iff₀ hd).1 hU
  nlinarith only [hlo, hstrict]

/-- All of `NormalizationExists`, including the scale and slope limits,
is a consequence of the single cited concentration theorem. -/
theorem normalization_exists : NormalizationExists := by
  classical
  intro hV f hf hnoconc M hM
  let P : ℝ → Prop := fun X => ∃ s : ℝ, 1 < s ∧ normalizationValue f X s = M
  have hP : ∀ᶠ X in atTop, P X := normalization_level_eventually hV f hf hnoconc M hM
  let s : ℝ → ℝ := fun X => if h : P X then Classical.choose h else 1
  have hsp (X : ℝ) : 0 < s X := by
    dsimp [s]
    split_ifs with h
    · exact lt_trans zero_lt_one (Classical.choose_spec h).1
    · norm_num
  have hsl : ∀ᶠ X in atTop, normalizationValue f X (s X) = M := by
    filter_upwards [hP] with X hX
    simpa [s, hX] using (Classical.choose_spec hX).2
  have hst := normalization_scales_tendsto_atTop hV f hf hnoconc s M
    (hsl.mono (fun X hX => ⟨hsp X, hX⟩))
  have hm (X : ℝ) := scaledMinimum_attained (Nat.primesLE ⌊X⌋₊)
    (fun p => 1 / (p : ℝ)) f (fun p => log p) (fun _ _ => by positivity) (s X)
  let c : ℝ → ℝ := fun X => Classical.choose (hm X)
  have hc (X : ℝ) := Classical.choose_spec (hm X)
  have hlev : ∀ᶠ X in atTop,
      cappedQuadratic (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ))
        (fun p => f p / s X) (fun p => log p) (c X) = M := by
    filter_upwards [hsl] with X hX
    exact (hc X).1.symm.trans hX
  refine ⟨{
    scale := s
    slope := c
    scale_pos := hsp
    scale_tendsto := hst
    slope_tendsto := normalization_slopes_tendsto f s c M hst (hlev.mono (fun _ h => h.le))
    minimum := ?_ }⟩
  filter_upwards [hlev] with X hX
  exact ⟨hX, fun y _ => (hc X).2 y⟩

end

end Erdos1122
