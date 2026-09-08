import Erdos1122.AdditiveExpansion
import Erdos1122.SecondMoment

/-! # Removing higher prime powers after clipping -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite retained set makes the unclipped error uniformly small outside
exactly the exceptional set counted by `higher_prime_power_union_bound`. -/
theorem higher_power_retained_bound (f : ℕ → ℝ) (hf : IsAdditive f)
    (F : Finset (ℕ × ℕ)) (n : ℕ) (hn : 0 < n) (K s c a : ℝ)
    (hgood : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ (p, k) ∉ F ∧ p ^ k ∣ n) :
    |clip K (f n / s - c * log n - a) -
      clip K ((∑ p ∈ n.primeFactors, (f p / s - c * log p)) - a)| ≤
      ∑ q ∈ F, |(f (q.1 ^ q.2) - f q.1) / s - c * ((q.2 : ℝ) - 1) * log q.1| := by
  let U := n.primeFactors.filter (fun p => 2 ≤ n.factorization p)
  let v := fun q : ℕ × ℕ => |(f (q.1 ^ q.2) - f q.1) / s - c * ((q.2 : ℝ) - 1) * log q.1|
  have hin : U.image (fun p => (p, n.factorization p)) ⊆ F := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    by_contra h
    exact hgood ⟨p, n.factorization p, (Nat.mem_primeFactors.1 (mem_filter.1 hp).1).1,
      (mem_filter.1 hp).2, h, Nat.ordProj_dvd n p⟩
  apply (clipped_higher_prime_power_bound f hf n hn K s c a).trans
  apply (abs_sum_le_sum_abs _ _).trans
  have he : (∑ p ∈ U, v (p, n.factorization p)) =
      ∑ q ∈ U.image (fun p => (p, n.factorization p)), v q := by
    rw [sum_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  change (∑ p ∈ U, v (p, n.factorization p)) ≤ ∑ q ∈ F, v q
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg hin (fun _ _ _ => abs_nonneg _)

/-- The reciprocal tail can be made arbitrarily small by a finite retained
set. The infinite sum has a proved summability hypothesis. -/
theorem higher_power_small_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset (ℕ × ℕ),
      (∑' q : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F},
        1 / ((q.val.1 : ℝ) ^ q.val.2)) < ε := by
  let I := {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ (∅ : Finset (ℕ × ℕ))}
  have ht := tendsto_tsum_compl_atTop_zero (fun q : I => 1 / ((q.val.1 : ℝ) ^ q.val.2))
  obtain ⟨U, hU⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  let F := U.image (fun q => q.val)
  refine ⟨F, ?_⟩
  let e : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F} ≃ {q : I // q ∉ U} := {
    toFun := fun q => ⟨⟨q.val, q.property.1, q.property.2.1, by simp⟩, by
      intro h
      exact q.property.2.2 (mem_image.2 ⟨_, h, rfl⟩)⟩
    invFun := fun q => ⟨q.val.val, q.val.property.1, q.val.property.2.1, by
      intro h
      obtain ⟨r, hr, he⟩ := mem_image.1 h
      exact q.property ((Subtype.ext he : r = q.val) ▸ hr)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have he := e.tsum_eq (fun q => 1 / ((q.val.val.1 : ℝ) ^ q.val.val.2))
  exact he.trans_lt hU

/-- The comparison `E_X |Y-Y_*|² → 0`, for arbitrary moving centers.
Only additivity and the scale and slope limits are required. -/
theorem higher_power_clipped_mean_tendsto (f : ℕ → ℝ) (hf : IsAdditive f)
    (s c a : ℝ → ℝ) (hs : Tendsto s atTop atTop) (hc : Tendsto c atTop (𝓝 0))
    (K : ℝ) (hK : 0 < K) :
    Tendsto (fun X : ℝ => initialMean (fun n =>
      (clip K (f n / s X - c X * log n - a X) -
       clip K ((∑ p ∈ n.primeFactors, (f p / s X - c X * log p)) - a X)) ^ 2) X)
      atTop (𝓝 0) := by
  let g := fun X n => clip K (f n / s X - c X * log n - a X) -
    clip K ((∑ p ∈ n.primeFactors, (f p / s X - c X * log p)) - a X)
  have hg (X : ℝ) (n : ℕ) : |g X n| ≤ 2 * K := by
    have h₁ := abs_clip_le hK.le (f n / s X - c X * log n - a X)
    have h₂ := abs_clip_le hK.le
      ((∑ p ∈ n.primeFactors, (f p / s X - c X * log p)) - a X)
    exact (abs_sub _ _).trans (by linarith only [h₁, h₂])
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨F, hF⟩ := higher_power_small_tail (ε / (8 * K ^ 2)) (by positivity)
  let T : ℝ := ∑' q : {q : ℕ × ℕ // q.1.Prime ∧ 2 ≤ q.2 ∧ q ∉ F},
    1 / ((q.val.1 : ℝ) ^ q.val.2)
  have hT : 0 ≤ T := tsum_nonneg (fun _ => by positivity)
  let B := fun X : ℝ => ∑ q ∈ F,
    |(f (q.1 ^ q.2) - f q.1) / s X - c X * ((q.2 : ℝ) - 1) * log q.1|
  have hB : Tendsto B atTop (𝓝 0) := by
    have hh := tendsto_finsetSum F (fun q _ =>
      ((hs.const_div_atTop (f (q.1 ^ q.2) - f q.1)).sub
        ((hc.mul_const ((q.2 : ℝ) - 1)).mul_const (log q.1))).abs)
    simpa only [sub_zero, zero_mul, abs_zero, sum_const_zero] using hh
  have hB2 : Tendsto (fun X => (B X) ^ 2) atTop (𝓝 0) := by simpa using hB.pow 2
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hB2.eventually (eventually_lt_nhds (show 0 < ε / 2 by positivity))] with X hX hBX
  let bad := fun n => ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ (p, k) ∉ F ∧ p ^ k ∣ n
  have hpoint (n : ℕ) (hn : n ∈ Ioc 0 ⌊X⌋₊) :
      (g X n) ^ 2 ≤ (B X) ^ 2 + if bad n then 4 * K ^ 2 else 0 := by
    by_cases hb : bad n
    · rw [if_pos hb]
      have hh := pow_le_pow_left₀ (abs_nonneg _) (hg X n) 2
      rw [sq_abs] at hh
      nlinarith [sq_nonneg (B X)]
    · rw [if_neg hb, add_zero]
      have hh := higher_power_retained_bound f hf F n (mem_Ioc.1 hn).1 K (s X) (c X) (a X) hb
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hcount : (#{n ∈ Ioc 0 ⌊X⌋₊ | bad n} : ℝ) ≤ X * T :=
    (higher_prime_power_union_bound ⌊X⌋₊ F).trans
      (mul_le_mul_of_nonneg_right (Nat.floor_le (show 0 ≤ X by linarith)) hT)
  have hsum := sum_le_sum hpoint
  have hconst : (∑ n ∈ Ioc 0 ⌊X⌋₊, if bad n then 4 * K ^ 2 else 0) =
      (#{n ∈ Ioc 0 ⌊X⌋₊ | bad n} : ℝ) * (4 * K ^ 2) := by
    rw [← sum_filter]
    simp
  rw [sum_add_distrib, hconst] at hsum
  simp only [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero] at hsum
  have hh : initialMean (fun n => (g X n) ^ 2) X ≤ (B X) ^ 2 + 4 * K ^ 2 * T := by
    apply (div_le_iff₀ (by linarith : 0 < X)).2
    have h₁ := mul_le_mul_of_nonneg_right (Nat.floor_le (show 0 ≤ X by linarith)) (sq_nonneg (B X))
    have h₂ := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 4 * K ^ 2 by positivity)
    nlinarith only [hsum, h₁, h₂]
  have hn : 0 ≤ initialMean (fun n => (g X n) ^ 2) X :=
    div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (by linarith)
  change dist (initialMean (fun n => (g X n) ^ 2) X) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  have htail := (lt_div_iff₀ (show 0 < 8 * K ^ 2 by positivity)).1 hF
  change T * (8 * K ^ 2) < ε at htail
  nlinarith only [hh, hBX, htail]

end

end Erdos1122
