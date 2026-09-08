import Erdos1122.ComparisonFamily
import Erdos1122.PrimeLogSquare

/-! # Projection onto the logarithm for the actual normalized prime values -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

namespace NormalizedFamily

variable {f : ℕ → ℝ} {M : ℝ}

/-- The numerator in (5.9), with the stationary small-prime contribution. -/
theorem comparison_log_pairing (N : NormalizedFamily f M) (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ X in atTop,
      |∑ p ∈ Nat.primesLE ⌊X⌋₊, clip K (N.residual X p) * log p / (p : ℝ)| ≤
        |N.slope X| + K * M * log X := by
  classical
  filter_upwards [N.minimum, eventually_ge_atTop (2 : ℝ)] with X hX hX2
  let P := Nat.primesLE ⌊X⌋₊
  let u := N.residual X
  have hlocal := hX.2.isLocalMin (Filter.univ_mem : Set.univ ∈ 𝓝 (N.slope X))
  have hstat := cappedQuadratic_stationary_abs P (fun p => 1 / (p : ℝ))
    (fun p => f p / N.scale X) (fun p => log p) (fun _ _ => by positivity) (N.slope X) hlocal
  have hstat' : (∑ p ∈ P, if |u p| < 1 then u p * log p / (p : ℝ) else 0) = N.slope X := by
    convert! hstat using 1
    apply sum_congr rfl
    intro p _
    dsimp [u, residual]
    simp only [div_eq_mul_inv]
    split_ifs <;> ring
  have hcap : (∑ p ∈ P, min ((u p) ^ 2) 1 / (p : ℝ)) ≤ M := by
    have hh := hX.1
    dsimp only [cappedQuadratic] at hh
    have he : (∑ p ∈ P, min ((u p) ^ 2) 1 / (p : ℝ)) =
        ∑ p ∈ P, (1 / (p : ℝ)) * min ((f p / N.scale X - N.slope X * log p) ^ 2) 1 := by
      apply sum_congr rfl
      intro p _
      dsimp [u, residual]
      ring
    rw [he]
    linarith [sq_nonneg (N.slope X)]
  have htail : (∑ p ∈ P, if |u p| < 1 then 0 else 1 / (p : ℝ)) ≤ M := by
    apply le_trans _ hcap
    apply sum_le_sum
    intro p _
    split_ifs with h
    · exact div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity)
    · rw [min_eq_right (by nlinarith [sq_abs (u p), abs_nonneg (u p)] : 1 ≤ (u p) ^ 2)]
  have heq : (∑ p ∈ P, clip K (u p) * log p / (p : ℝ)) = N.slope X +
      ∑ p ∈ P, if |u p| < 1 then 0 else clip K (u p) * log p / (p : ℝ) := by
    rw [← hstat', ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    split_ifs with h
    · rw [clip_eq_self (h.le.trans hK)]
      ring
    · ring
  have hlogX : 0 ≤ log X := (log_pos (by linarith)).le
  have ht : |∑ p ∈ P, if |u p| < 1 then 0 else clip K (u p) * log p / (p : ℝ)| ≤
      (K * log X) * (∑ p ∈ P, if |u p| < 1 then 0 else 1 / (p : ℝ)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hpX : (p : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).1 (Nat.mem_primesLE.1 hp).1
    have hlogp : 0 ≤ log p := (log_pos (by exact_mod_cast hpprime.one_lt)).le
    split_ifs
    · simp
    · rw [abs_div, abs_mul, abs_of_pos hp0, abs_of_nonneg hlogp]
      have hh := div_le_div_of_nonneg_right
        (mul_le_mul (abs_clip_le (by linarith) (u p)) (log_le_log hp0 hpX) hlogp
          (by linarith : 0 ≤ K)) hp0.le
      exact hh.trans_eq (by ring)
  rw [heq]
  have hh := (abs_add_le (N.slope X)
    (∑ p ∈ P, if |u p| < 1 then 0 else clip K (u p) * log p / (p : ℝ))).trans
      (add_le_add le_rfl ht)
  have hm := mul_le_mul_of_nonneg_left htail (mul_nonneg (show 0 ≤ K by linarith) hlogX)
  nlinarith only [hh, hm]

/-- The actual prime projection in (5.10). The denominator is bounded
below using Chebyshev, and the lower mass and numerator come from the
normalizing minimum. This estimate is uniform over every real slope `b`. -/
theorem comparison_prime_projection (N : NormalizedFamily f M) (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ X in atTop, ∀ b : ℝ,
      M - (N.slope X) ^ 2 -
        (8 / log 2) * (|N.slope X| / log X + K * M) ^ 2 ≤
      ∑ p ∈ Nat.primesLE ⌊X⌋₊, (clip K (N.residual X p) - b * log p) ^ 2 / (p : ℝ) := by
  filter_upwards [N.minimum, N.comparison_log_pairing K hK, primeLogSquare_eventually_lower,
    eventually_ge_atTop (2 : ℝ)] with X hX hpair hden hX2
  intro b
  let P := Nat.primesLE ⌊X⌋₊
  let w := fun p : ℕ => 1 / (p : ℝ)
  let v := fun p : ℕ => clip K (N.residual X p)
  have hlog : 0 < log X := log_pos (by linarith)
  have hdenpos : 0 < primeLogSquare X :=
    lt_of_lt_of_le (mul_pos (by positivity) (sq_pos_of_pos hlog)) hden
  have heB : quadraticMass P w (fun p => log p) = primeLogSquare X := by
    unfold quadraticMass primeLogSquare
    apply sum_congr rfl
    intro p _
    dsimp [w]
    ring
  have heR : weightedPairing P w v (fun p => log p) =
      ∑ p ∈ P, clip K (N.residual X p) * log p / (p : ℝ) := by
    unfold weightedPairing
    apply sum_congr rfl
    intro p _
    dsimp [w, v]
    ring
  have hmass : M - (N.slope X) ^ 2 ≤ quadraticMass P w v := by
    have hh := (weighted_clipped_square_bounds P w (N.residual X)
      (fun _ _ => by positivity) hK).1
    have hm := hX.1
    dsimp only [cappedQuadratic] at hm
    change M - (N.slope X) ^ 2 ≤ ∑ p ∈ P, w p * (v p) ^ 2
    dsimp only [v, residual] at hh ⊢
    linarith only [hh, hm]
  have hp := quadratic_projection_lower_of_bounds P w v (fun p => log p)
    b (M - (N.slope X) ^ 2) (|N.slope X| + K * M * log X)
    (by simpa only [heB] using hdenpos) hmass (by simpa only [heR] using hpair)
  rw [heB] at hp
  have hd := div_le_div_of_nonneg_left (sq_nonneg (|N.slope X| + K * M * log X))
    (mul_pos (by positivity : 0 < log (2 : ℝ) / 8) (sq_pos_of_pos hlog)) hden
  have he : (|N.slope X| + K * M * log X) ^ 2 / ((log 2 / 8) * (log X) ^ 2) =
      (8 / log 2) * (|N.slope X| / log X + K * M) ^ 2 := by
    field_simp
  rw [he] at hd
  have hh : M - (N.slope X) ^ 2 -
      (8 / log 2) * (|N.slope X| / log X + K * M) ^ 2 ≤
      quadraticMass P w (fun p => v p - b * log p) := by linarith only [hp, hd]
  apply hh.trans_eq
  unfold quadraticMass
  apply sum_congr rfl
  intro p _
  dsimp [w, v]
  ring

theorem comparison_prime_projection_lower_tendsto (N : NormalizedFamily f M) (K : ℝ) :
    Tendsto (fun X : ℝ => M - (N.slope X) ^ 2 -
      (8 / log 2) * (|N.slope X| / log X + K * M) ^ 2)
      atTop (𝓝 (M - (8 / log 2) * K ^ 2 * M ^ 2)) := by
  have hr : Tendsto (fun X : ℝ => |N.slope X| / log X) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using N.slope_tendsto.abs.mul (tendsto_log_atTop.inv_tendsto_atTop)
  convert! ((N.slope_tendsto.pow 2).const_sub M).sub
    (((hr.add_const (K * M)).pow 2).const_mul (8 / log 2)) using 1
  simp [mul_pow, mul_assoc]

end NormalizedFamily

end

end Erdos1122
