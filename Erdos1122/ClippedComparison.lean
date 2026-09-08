import Erdos1122.MixedMoment
import Erdos1122.HigherPowerComparison

/-! # Lemma 5.1: clipping the values and the prime contributions -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

/-- Apply the three scalar clipping cases to the prime divisors of one
integer. This is a finite identity and inequality, before any moment input. -/
theorem clipped_divisor_pointwise (P : Finset ℕ) (u : ℕ → ℝ) (K a : ℝ)
    (hK : 1 < K) (n : ℕ) :
    let small := fun p => if |u p| ≤ 1 then u p else 0
    let S := divisorSum P small n - a
    let T := P.filter (fun p => 1 < |u p|)
    (clip K (divisorSum P u n - a) - (divisorSum P (fun p => clip K (u p)) n - a)) ^ 2 ≤
      S ^ 4 / K ^ 2 + 4 * S ^ 2 * (if ∃ p ∈ T, p ∣ n then 1 else 0) +
        9 * K ^ 2 * (primeDivisorCount T n : ℝ) * ((primeDivisorCount T n : ℝ) - 1) := by
  dsimp only
  let small := fun p => if |u p| ≤ 1 then u p else 0
  let T := P.filter (fun p => 1 < |u p|)
  let t := T.filter (fun p => p ∣ n)
  have hsum : divisorSum P u n - a =
      (divisorSum P small n - a) + ∑ p ∈ t, u p := by
    dsimp [divisorSum, t, T]
    rw [sum_filter, sum_filter, sub_add_eq_add_sub, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    dsimp [small]
    by_cases hd : p ∣ n <;> by_cases hu : |u p| ≤ 1 <;>
      simp [hd, hu, not_lt.mpr, lt_of_not_ge]
  have hclip : divisorSum P (fun p => clip K (u p)) n - a =
      (divisorSum P small n - a) + ∑ p ∈ t, clip K (u p) := by
    dsimp [divisorSum, t, T]
    rw [sum_filter, sum_filter, sub_add_eq_add_sub, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    dsimp [small]
    by_cases hd : p ∣ n
    · by_cases hu : |u p| ≤ 1
      · simp [hd, hu, not_lt.mpr hu, clip_eq_self (hu.trans hK.le)]
      · simp [hd, hu, lt_of_not_ge hu]
    · simp [hd]
  rw [hsum, hclip]
  have hh := clip_finite_tail_error_sq t u (by linarith : 0 < K) (divisorSum P small n - a)
  have hne : t.Nonempty ↔ ∃ p ∈ T, p ∣ n := by simp only [t, filter_nonempty_iff]
  simpa only [hne, primeDivisorCount, t, mul_ite, mul_one, mul_zero] using hh

/-- A prime-divisor sum can be restricted to the prime factors of a
positive integer whenever the cutoff includes that integer. -/
theorem divisorSum_eq_primeFactors (u : ℕ → ℝ) (X : ℝ) (n : ℕ)
    (hn : 0 < n) (hnX : n ≤ ⌊X⌋₊) :
    divisorSum (Nat.primesLE ⌊X⌋₊) u n = ∑ p ∈ n.primeFactors, u p := by
  unfold divisorSum
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨_, hp⟩, hd⟩
    exact ⟨hp, hd, hn.ne'⟩
  · rintro ⟨hp, hd, _⟩
    exact ⟨⟨(Nat.le_of_dvd hn hd).trans hnX, hp⟩, hd⟩

namespace NormalizedFamily

variable {f : ℕ → ℝ} {M : ℝ}

def strongObservable (N : NormalizedFamily f M) (K X : ℝ) (n : ℕ) : ℝ :=
  clip K (divisorSum (Nat.primesLE ⌊X⌋₊) (N.residual X) n - N.offset X)

def higherPowerError (N : NormalizedFamily f M) (K X : ℝ) : ℝ :=
  initialMean (fun n => (N.observable K X n - N.strongObservable K X n) ^ 2) X

theorem higherPowerError_tendsto (N : NormalizedFamily f M) (hf : IsAdditive f)
    (K : ℝ) (hK : 0 < K) : Tendsto (N.higherPowerError K) atTop (𝓝 0) := by
  apply (higher_power_clipped_mean_tendsto f hf N.scale N.slope N.offset
    N.scale_tendsto N.slope_tendsto K hK).congr
  intro X
  unfold higherPowerError initialMean observable strongObservable
  congr 1
  apply sum_congr rfl
  intro n hn
  dsimp only
  rw [divisorSum_eq_primeFactors _ X n (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2]
  rfl

end NormalizedFamily

set_option maxHeartbeats 800000 in
/-- Lemma 5.1 with all finite clipping cases, the mixed moment, and the
higher-prime-power comparison assembled. -/
theorem clipped_comparison : ClippedComparison := by
  intro hE h55
  obtain ⟨E, hEpos, hE⟩ := stronglyAdditive_fourth_moment_mass hE
  obtain ⟨C55, hC55, h55⟩ := h55
  let C : ℝ := 4 * E + 8 * C55 + 18
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf K M hK hM hMq N
  let R : ℝ := M / K ^ 2 + M ^ 2 * log (2 / M) + K ^ 2 * M ^ 2
  let B := fun X : ℝ => C * R + 8 / log X + 2 * N.higherPowerError K X
  have hB : Tendsto B atTop (𝓝 (C * R)) := by
    simpa [B] using (tendsto_const_nhds.add (tendsto_log_atTop.const_div_atTop 8)).add
      ((N.higherPowerError_tendsto hf K (by linarith)).const_mul 2)
  have hpoint : ∀ᶠ X in atTop, N.discrepancy K X ≤ B X := by
    filter_upwards [N.minimum, h55 M hM hMq, eventually_ge_atTop (2 : ℝ)] with X hNX h55X hX
    let P := Nat.primesLE ⌊X⌋₊
    let u := N.residual X
    let a := fun p => if |u p| ≤ 1 then u p else 0
    let S₀ := divisorSum P a
    let μ := ∑ p ∈ P, a p / (p : ℝ)
    let T := P.filter (fun p => 1 < |u p|)
    have hcap : (∑ p ∈ P, min ((u p) ^ 2) 1 / (p : ℝ)) ≤ M := by
      have hh := hNX.1
      dsimp only [cappedQuadratic] at hh
      change (∑ p ∈ P, min ((f p / N.scale X - N.slope X * log p) ^ 2) 1 / (p : ℝ)) ≤ M
      simp only [div_eq_mul_inv, mul_comm, mul_one] at hh ⊢
      linarith [sq_nonneg (N.slope X)]
    have hp (p : ℕ) (hpp : p ∈ P) : S₀ p = a p := by
      exact (divisorSum_prime P a (fun _ hq => Nat.prime_of_mem_primesLE hq)
        p (Nat.prime_of_mem_primesLE hpp)).trans (if_pos hpp)
    have ha (p : ℕ) : |a p| ≤ 1 ∧ |a p| ^ 2 ≤ min ((u p) ^ 2) 1 := by
      dsimp [a]
      split_ifs with hu
      · refine ⟨hu, ?_⟩
        rw [sq_abs, min_eq_left (by nlinarith [sq_abs (u p), abs_nonneg (u p)] : (u p) ^ 2 ≤ 1)]
      · simp only [abs_zero, zero_pow (by decide : 2 ≠ 0)]
        exact ⟨zero_le_one, le_min (sq_nonneg _) zero_le_one⟩
    have hm : primeMoment S₀ X 2 ≤ M := by
      apply le_trans _ hcap
      apply sum_le_sum
      intro p hpp
      rw [hp p hpp]
      exact div_le_div_of_nonneg_right (ha p).2 (by positivity)
    have hm4 : primeMoment S₀ X 4 ≤ M := by
      have hh := primeMoment_fourth_le S₀ X 1 (fun p hpp => by rw [hp p hpp]; exact (ha p).1)
      simpa using hh.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1 ^ 2))
    have hcenter : primeCenter S₀ X = μ := by
      apply sum_congr rfl
      intro p hpp
      rw [hp p hpp]
    have h₄ := hE S₀ (divisorSum_stronglyAdditive P a (fun _ hq => Nat.prime_of_mem_primesLE hq)) X hX
    rw [hcenter] at h₄
    have hpow := pow_le_pow_left₀ (show 0 ≤ primeMoment S₀ X 2 by unfold primeMoment; positivity) hm 2
    have h₄' : initialMean (fun n => (S₀ n - μ) ^ 4) X ≤ E * (M ^ 2 + M) :=
      h₄.trans (mul_le_mul_of_nonneg_left (add_le_add hpow hm4) hEpos.le)
    have hTmass : (∑ p ∈ T, 1 / (p : ℝ)) ≤ M := by
      apply le_trans _ hcap
      rw [sum_filter]
      apply sum_le_sum
      intro p _
      split_ifs with hu
      · rw [min_eq_right (by nlinarith [sq_abs (u p)] : 1 ≤ (u p) ^ 2)]
      · exact div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity)
    have h₂ := prime_divisor_factorial_mean_le_real T
      (fun _ hq => Nat.prime_of_mem_primesLE (mem_filter.1 hq).1) X M (by linarith) hTmass
    have hmix := h55X u hcap
    change initialMean (fun n => (S₀ n - μ) ^ 2 *
      if ∃ p ∈ P, 1 < |u p| ∧ p ∣ n then 1 else 0) X ≤ C55 * M ^ 2 * log (2 / M) + 1 / log X at hmix
    have hi (n : ℕ) : (∃ p ∈ T, p ∣ n) ↔ ∃ p ∈ P, 1 < |u p| ∧ p ∣ n := by
      simp only [T, mem_filter]
      constructor
      · rintro ⟨p, ⟨hp, hu⟩, hd⟩
        exact ⟨p, hp, hu, hd⟩
      · rintro ⟨p, hp, hu, hd⟩
        exact ⟨p, ⟨hp, hu⟩, hd⟩
    have hfinite : initialMean (fun n =>
        (N.strongObservable K X n - (N.comparison K X n - N.offset X)) ^ 2) X ≤
        (E * (M ^ 2 + M)) / K ^ 2 + 4 * (C55 * M ^ 2 * log (2 / M) + 1 / log X) + 9 * K ^ 2 * M ^ 2 := by
      have hh := sum_le_sum (s := Ioc 0 ⌊X⌋₊) (fun n _ => clipped_divisor_pointwise P u K μ hK n)
      change (∑ n ∈ Ioc 0 ⌊X⌋₊, (clip K (divisorSum P u n - μ) -
        (divisorSum P (fun p => clip K (u p)) n - μ)) ^ 2) ≤
        ∑ n ∈ Ioc 0 ⌊X⌋₊, ((S₀ n - μ) ^ 4 / K ^ 2 +
          4 * (S₀ n - μ) ^ 2 * (if ∃ p ∈ T, p ∣ n then 1 else 0) +
          9 * K ^ 2 * (primeDivisorCount T n : ℝ) * ((primeDivisorCount T n : ℝ) - 1)) at hh
      simp only [hi, sum_add_distrib, ← sum_div, mul_assoc, ← mul_sum] at hh
      have hh' := div_le_div_of_nonneg_right hh (show 0 ≤ X by linarith)
      change initialMean (fun n => (clip K (divisorSum P u n - μ) -
        (divisorSum P (fun p => clip K (u p)) n - μ)) ^ 2) X ≤ _
      have h₄div := div_le_div_of_nonneg_right h₄' (sq_nonneg K)
      have h₂mul := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 9 * K ^ 2 by positivity)
      dsimp only [initialMean] at h₄div hmix ⊢
      simp only [div_eq_mul_inv] at hh' h₄div hmix h₂mul ⊢
      nlinarith only [hh', h₄div, hmix, h₂mul]
    have hdiff : N.discrepancy K X ≤
        2 * N.higherPowerError K X + 2 * initialMean (fun n =>
          (N.strongObservable K X n - (N.comparison K X n - N.offset X)) ^ 2) X := by
      unfold NormalizedFamily.discrepancy NormalizedFamily.higherPowerError initialMean
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, mul_sum, mul_sum, ← sum_add_distrib]
      apply div_le_div_of_nonneg_right _ (by linarith)
      apply sum_le_sum
      intro n _
      nlinarith [sq_nonneg (N.observable K X n - 2 * N.strongObservable K X n +
        (N.comparison K X n - N.offset X))]
    have hlog : 0 ≤ log (2 / M) := (log_pos ((lt_div_iff₀ hM).2 (by linarith))).le
    have h₄simple : (E * (M ^ 2 + M)) / K ^ 2 ≤ 2 * E * (M / K ^ 2) := by
      apply (div_le_div_of_nonneg_right (show E * (M ^ 2 + M) ≤ 2 * E * M by
        nlinarith [mul_nonneg hEpos.le (show 0 ≤ M - M ^ 2 by nlinarith)]) (sq_nonneg K)).trans_eq
      ring
    have hmain : 4 * E * (M / K ^ 2) + 8 * C55 * (M ^ 2 * log (2 / M)) + 18 * (K ^ 2 * M ^ 2) ≤ C * R := by
      dsimp [C, R]
      nlinarith [mul_nonneg (show 0 ≤ 8 * C55 + 18 by positivity) (show 0 ≤ M / K ^ 2 by positivity),
        mul_nonneg (show 0 ≤ 4 * E + 18 by positivity) (mul_nonneg (sq_nonneg M) hlog),
        mul_nonneg (show 0 ≤ 4 * E + 8 * C55 by positivity) (show 0 ≤ K ^ 2 * M ^ 2 by positivity)]
    dsimp only [B]
    simp only [div_eq_mul_inv] at hfinite h₄simple hmain ⊢
    nlinarith only [hdiff, hfinite, h₄simple, hmain]
  have hnonneg (X : ℝ) : 0 ≤ N.discrepancy K X :=
    initialMean_square_nonneg _ X
  have hbound : IsBoundedUnder (· ≤ ·) atTop (N.discrepancy K) := by
    refine ⟨C * R + 1, ?_⟩
    change ∀ᶠ X in atTop, N.discrepancy K X ≤ C * R + 1
    filter_upwards [hpoint, hB.eventually (eventually_lt_nhds (lt_add_one (C * R)))] with X hX hBX
    exact hX.trans hBX.le
  refine ⟨hbound, ?_⟩
  have hh := limsup_le_limsup hpoint (isCoboundedUnder_le_of_le atTop hnonneg) hB.isBoundedUnder_le
  rwa [hB.limsup_eq] at hh

end

end Erdos1122
