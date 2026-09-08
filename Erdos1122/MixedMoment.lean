import Erdos1122.SecondMoment
import Erdos1122.ComparisonFamily

/-! # The mixed tail-prime moment (5.5) -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

/-- Cauchy--Schwarz for the change of the prime center at an arbitrary scale. -/
theorem primeCenter_difference_sq_le (f : ℕ → ℝ) (X Y : ℝ)
    (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    (primeCenter f X - primeCenter f Y) ^ 2 ≤
      primeMoment f X 2 *
        (∑ p ∈ Nat.primesLE ⌊X⌋₊, if Y < (p : ℝ) then 1 / (p : ℝ) else 0) := by
  let U := (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ => Y < (p : ℝ))
  have he : primeCenter f X - primeCenter f Y = ∑ p ∈ U, f p / (p : ℝ) := by
    have hr := congrArg (fun P : Finset ℕ => ∑ p ∈ P, f p / (p : ℝ)) (primes_restrict X Y hY hYX)
    rw [sum_filter] at hr
    unfold primeCenter
    rw [← hr, ← sum_sub_distrib]
    dsimp [U]
    rw [sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases h : (p : ℝ) ≤ Y <;> simp [h, not_lt.mpr, lt_of_not_ge]
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul U
    (f := fun p => |f p| ^ 2 / (p : ℝ)) (g := fun p => 1 / (p : ℝ))
    (r := fun p => f p / (p : ℝ))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun p _ => by
      rw [sq_abs]
      apply le_of_eq
      ring)
  have hm : (∑ p ∈ U, |f p| ^ 2 / (p : ℝ)) ≤ primeMoment f X 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  rw [he]
  have hh := hc.trans (mul_le_mul_of_nonneg_right hm (by positivity))
  simpa only [U, sum_filter] using hh

theorem divisorSum_mul_of_zero (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p.Prime) (ha : a p = 0) (n : ℕ) :
    divisorSum P a (p * n) = divisorSum P a n := by
  unfold divisorSum
  apply sum_congr rfl
  intro q hq
  by_cases hqp : q = p
  · subst q
    simp [ha]
  · have hnd : ¬ q ∣ p := by
      simpa only [Nat.prime_dvd_prime_iff_eq (hP q hq) hp] using hqp
    simp [(hP q hq).dvd_mul, hnd]

/-- Reindex the multiples of a prime, retaining the real cutoff exactly. -/
theorem mean_on_multiples (g : ℕ → ℝ) (X : ℝ) (p : ℕ) (hp : 0 < p) :
    initialMean (fun n => g n * if p ∣ n then 1 else 0) X =
      (1 / (p : ℝ)) * initialMean (fun n => g (p * n)) (X / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : (Ioc 0 ⌊X⌋₊).filter (fun n => p ∣ n) =
      (Ioc 0 (⌊X⌋₊ / p)).image (fun n => p * n) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨hn, hnX⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · exact Nat.pos_of_mul_pos_left hn
      · exact (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hnX)
    · rintro ⟨m, ⟨hm, hmX⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hp hm, ?_⟩, dvd_mul_right _ _⟩
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).1 hmX
  unfold initialMean
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← sum_filter, he, sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp h),
    Nat.floor_div_natCast]
  field_simp

/-- The purely finite reduction behind (5.5). -/
theorem mixed_moment_finite (C : ℝ) (hC : 0 < C)
    (hTK : ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ y : ℝ, 1 ≤ y →
      initialMean (fun n => (f n - primeCenter f y) ^ 2) y ≤ C * primeMoment f y 2)
    (X M : ℝ) (hX : 2 ≤ X) (_hM : 0 ≤ M) (P T : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hT : T ⊆ Nat.primesLE ⌊X⌋₊)
    (hz : ∀ p ∈ T, a p = 0) (hm : primeMoment (divisorSum P a) X 2 ≤ M) :
    initialMean (fun n => (divisorSum P a n - primeCenter (divisorSum P a) X) ^ 2 *
      if ∃ p ∈ T, p ∣ n then 1 else 0) X ≤
        2 * C * M * (∑ p ∈ T, 1 / (p : ℝ)) + 2 * M * primeTailKernel T X := by
  let f := divisorSum P a
  have hf : IsStronglyAdditive f := divisorSum_stronglyAdditive P a hP
  have hone (p : ℕ) (hp : p ∈ T) :
      initialMean (fun n => (f n - primeCenter f X) ^ 2 * if p ∣ n then 1 else 0) X ≤
        (1 / (p : ℝ)) * (2 * C * M + 2 * M *
          (∑ q ∈ Nat.primesLE ⌊X⌋₊, if X / (p : ℝ) < (q : ℝ) then 1 / (q : ℝ) else 0)) := by
    have hprime := Nat.prime_of_mem_primesLE (hT hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).1 (Nat.mem_primesLE.1 (hT hp)).1
    have hy : 1 ≤ X / (p : ℝ) := (le_div_iff₀ hp0).2 (by simpa using hpX)
    have hyX : X / (p : ℝ) ≤ X := div_le_self (by linarith)
      (by exact_mod_cast hprime.one_lt.le)
    rw [mean_on_multiples _ X p hprime.pos]
    have he : (fun n => (f (p * n) - primeCenter f X) ^ 2) =
        (fun n => (f n - primeCenter f X) ^ 2) := by
      funext n
      dsimp only [f]
      rw [divisorSum_mul_of_zero P a hP p hprime (hz p hp)]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have htk := (hTK f hf (X / (p : ℝ)) hy).trans
      (mul_le_mul_of_nonneg_left ((primeMoment_mono f 2 hyX).trans hm) hC.le)
    have hs := second_moment_center_shift f (primeCenter f X) (primeCenter f (X / (p : ℝ)))
      (X / (p : ℝ)) (by linarith)
    have hc := (primeCenter_difference_sq_le f X (X / (p : ℝ)) (by positivity) hyX).trans
      (mul_le_mul_of_nonneg_right hm (by positivity))
    nlinarith only [htk, hs, hc]
  calc
    _ ≤ ∑ p ∈ T, initialMean (fun n => (f n - primeCenter f X) ^ 2 * if p ∣ n then 1 else 0) X := by
      unfold initialMean
      rw [← sum_div, sum_comm]
      apply div_le_div_of_nonneg_right _ (by linarith)
      apply sum_le_sum
      intro n _
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      split_ifs with hex
      · obtain ⟨p, hp, hpn⟩ := hex
        have hh := single_le_sum (s := T) (f := fun q => if q ∣ n then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) hp
        simpa [hpn] using hh
      · exact sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    _ ≤ ∑ p ∈ T, (1 / (p : ℝ)) * (2 * C * M + 2 * M *
        (∑ q ∈ Nat.primesLE ⌊X⌋₊, if X / (p : ℝ) < (q : ℝ) then 1 / (q : ℝ) else 0)) :=
      sum_le_sum hone
    _ = _ := by
      unfold primeTailKernel
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro p _
      ring

/-- The mixed moment in the manuscript follows from Ruzsa and the
unconditional prime-tail bound. No new arithmetic input is assumed. -/
theorem estimate55_of_ruzsa (hR : Ruzsa) : Estimate55 := by
  obtain ⟨C, hC, hTK⟩ := stronglyAdditive_second_moment_all_scales hR
  have hA : 0 < primeTailConstant := by unfold primeTailConstant; positivity
  have hlog2 : 0 < log (2 : ℝ) := by positivity
  refine ⟨2 * C / log 2 + 2 * primeTailConstant + 1, by positivity, ?_⟩
  intro M hM hMq
  have hlog : log 2 ≤ log (2 / M) := log_le_log (by norm_num)
    ((le_div_iff₀ hM).2 (by linarith))
  have htarget : 0 < M ^ 2 * log (2 / M) := mul_pos (sq_pos_of_pos hM) (hlog2.trans_le hlog)
  have herr : Tendsto (fun X : ℝ => 2 * M * (log 4 / log X)) atTop (𝓝 0) := by
    simpa using primeTailKernel_error_tendsto.const_mul (2 * M)
  filter_upwards [primeTailKernel_eventually M hM hMq, eventually_ge_atTop (2 : ℝ),
    herr.eventually (eventually_lt_nhds htarget)] with X htail hX he
  intro u hmass
  let P := Nat.primesLE ⌊X⌋₊
  let a := fun p => if |u p| ≤ 1 then u p else 0
  let T := P.filter (fun p => 1 < |u p|)
  let f := divisorSum P a
  have hp (p : ℕ) (hp : p ∈ P) : f p = a p := by
    exact (divisorSum_prime P a (fun _ hq => Nat.prime_of_mem_primesLE hq)
      p (Nat.prime_of_mem_primesLE hp)).trans (if_pos hp)
  have hsmall (p : ℕ) : |a p| ^ 2 ≤ min ((u p) ^ 2) 1 := by
    dsimp [a]
    split_ifs with h
    · rw [sq_abs, min_eq_left (by nlinarith [sq_abs (u p), abs_nonneg (u p)] : (u p) ^ 2 ≤ 1)]
    · simpa only [abs_zero, zero_pow (by decide : 2 ≠ 0)] using
        (le_min (sq_nonneg (u p)) zero_le_one)
  have hm : primeMoment f X 2 ≤ M := by
    apply le_trans _ hmass
    apply sum_le_sum
    intro p hpp
    rw [hp p hpp]
    exact div_le_div_of_nonneg_right (hsmall p) (by positivity)
  have hT : T ⊆ Nat.primesLE ⌊X⌋₊ := filter_subset _ _
  have hz (p : ℕ) (hpp : p ∈ T) : a p = 0 := by
    simp [a, not_le_of_gt (mem_filter.1 hpp).2]
  have hmassT : (∑ p ∈ T, 1 / (p : ℝ)) ≤ M := by
    calc
      _ = ∑ p ∈ T, min ((u p) ^ 2) 1 / (p : ℝ) := by
        apply sum_congr rfl
        intro p hpp
        have hu := (mem_filter.1 hpp).2
        rw [min_eq_right (by nlinarith [sq_abs (u p)] : 1 ≤ (u p) ^ 2)]
      _ ≤ ∑ p ∈ P, min ((u p) ^ 2) 1 / (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun _ _ _ => div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity))
      _ ≤ M := hmass
  have hcenter : primeCenter f X = ∑ p ∈ P, a p / (p : ℝ) := by
    apply sum_congr rfl
    intro p hpp
    rw [hp p hpp]
  have hiff (n : ℕ) : (∃ p ∈ T, p ∣ n) ↔ ∃ p ∈ P, 1 < |u p| ∧ p ∣ n := by
    simp only [T, mem_filter]
    constructor
    · rintro ⟨p, ⟨hp, hu⟩, hd⟩
      exact ⟨p, hp, hu, hd⟩
    · rintro ⟨p, hp, hu, hd⟩
      exact ⟨p, ⟨hp, hu⟩, hd⟩
  have hh := mixed_moment_finite C hC hTK X M hX hM.le P T a
    (fun _ hq => Nat.prime_of_mem_primesLE hq) hT hz hm
  change initialMean (fun n => (f n - primeCenter f X) ^ 2 *
    if ∃ p ∈ T, p ∣ n then 1 else 0) X ≤ _ at hh
  simp only [hiff, hcenter] at hh
  have h₁ := mul_le_mul_of_nonneg_left hmassT (show 0 ≤ 2 * C * M by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (htail T hT hmassT) (show 0 ≤ 2 * M by positivity)
  have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (2 * C / log 2) * M ^ 2 by positivity)
  have hcancel : (2 * C / log 2) * M ^ 2 * log 2 = 2 * C * M ^ 2 := by field_simp
  rw [hcancel] at hlogmul
  have herror : 0 ≤ 1 / log X := div_nonneg zero_le_one (log_pos (by linarith)).le
  change initialMean (fun n => (f n - ∑ p ∈ P, a p / (p : ℝ)) ^ 2 *
    if ∃ p ∈ P, 1 < |u p| ∧ p ∣ n then 1 else 0) X ≤ _
  nlinarith only [hh, h₁, h₂, he, hlogmul, herror]

end

end Erdos1122
