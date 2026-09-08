import Erdos1122.AssemblyStatements

/-! # The concrete strongly additive family used in the main assembly -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

theorem divisorSum_prime (P : Finset ℕ) (a : ℕ → ℝ) (hP : ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : q.Prime) : divisorSum P a q = if q ∈ P then a q else 0 := by
  classical
  unfold divisorSum
  calc
    _ = ∑ p ∈ P, if p = q then a p else 0 := by
      apply sum_congr rfl
      intro p hp
      simp only [Nat.prime_dvd_prime_iff_eq (hP p hp) hq]
    _ = _ := by simp

theorem divisorSum_stronglyAdditive (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) : IsStronglyAdditive (divisorSum P a) := by
  classical
  intro n hn
  calc
    divisorSum P a n = ∑ p ∈ P ∩ n.primeFactors, a p := by
      unfold divisorSum
      rw [← sum_filter]
      congr 1
      ext p
      simp only [mem_filter, mem_inter, Nat.mem_primeFactors]
      exact ⟨fun h => ⟨h.1, hP p h.1, h.2, hn.ne'⟩, fun h => ⟨h.1, h.2.2.1⟩⟩
    _ = ∑ p ∈ n.primeFactors, divisorSum P a p := by
      have he : P ∩ n.primeFactors = n.primeFactors.filter (fun p => p ∈ P) := by
        ext p
        simp [and_comm]
      rw [he, sum_filter]
      apply sum_congr rfl
      intro p hp
      rw [divisorSum_prime P a hP p (Nat.mem_primeFactors.1 hp).1]

/-- Lemma 2.1 remains valid when the prime-mass bound holds eventually.
Changing a family at bounded cutoffs leaves every inner limsup unchanged. -/
theorem short_interval_second_moment_eventually (hM : Mangerel) (hE : Elliott)
    (z : ℝ → ℕ → ℝ) (L V : ℝ) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hz : ∀ X, IsStronglyAdditive (z X))
    (hcoeff : ∀ X p, p.Prime → |z X p| ≤ L)
    (hmass : ∀ᶠ X in atTop, primeMoment (z X) X 2 ≤ V) :
    Tendsto (fun H : ℕ => limsup (fun X : ℝ => shortIntervalMoment H (z X) X 2) atTop)
      atTop (𝓝 0) := by
  classical
  let z' : ℝ → ℕ → ℝ := fun X => if primeMoment (z X) X 2 ≤ V then z X else fun _ => 0
  have hzero : IsStronglyAdditive (fun _ : ℕ => (0 : ℝ)) := by intro n _; simp
  have hz' (X : ℝ) : IsStronglyAdditive (z' X) := by
    dsimp [z']
    split_ifs
    · exact hz X
    · exact hzero
  have hcoeff' (X : ℝ) (p : ℕ) (hp : p.Prime) : |z' X p| ≤ L := by
    dsimp [z']
    split_ifs
    · exact hcoeff X p hp
    · simpa using hL
  have hmass' (X : ℝ) (_hX : 2 ≤ X) : primeMoment (z' X) X 2 ≤ V := by
    dsimp [z']
    split_ifs with h
    · exact h
    · simpa [primeMoment] using hV
  have ht := short_interval_second_moment hM hE z' L V hL hV hz' hcoeff' hmass'
  have he (H : ℕ) : limsup (fun X : ℝ => shortIntervalMoment H (z' X) X 2) atTop =
      limsup (fun X : ℝ => shortIntervalMoment H (z X) X 2) atTop := by
    apply Filter.limsup_congr
    filter_upwards [hmass] with X hX
    simp [z', hX]
  simpa only [he] using ht

namespace NormalizedFamily

variable {f : ℕ → ℝ} {M : ℝ}

theorem comparison_stronglyAdditive (N : NormalizedFamily f M) (K X : ℝ) :
    IsStronglyAdditive (N.comparison K X) :=
  divisorSum_stronglyAdditive _ _ (fun _ hp => Nat.prime_of_mem_primesLE hp)

theorem comparison_prime (N : NormalizedFamily f M) (K X : ℝ) (p : ℕ) (hp : p.Prime) :
    N.comparison K X p = if p ∈ Nat.primesLE ⌊X⌋₊ then clip K (N.residual X p) else 0 :=
  divisorSum_prime _ _ (fun _ hq => Nat.prime_of_mem_primesLE hq) p hp

theorem comparison_coeff (N : NormalizedFamily f M) (K : ℝ) (hK : 0 ≤ K)
    (X : ℝ) (p : ℕ) (hp : p.Prime) : |N.comparison K X p| ≤ K := by
  rw [N.comparison_prime K X p hp]
  split_ifs
  · exact abs_clip_le hK _
  · simpa using hK

theorem comparison_mass (N : NormalizedFamily f M) (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ X in atTop, primeMoment (N.comparison K X) X 2 ≤ K ^ 2 * M := by
  filter_upwards [N.minimum] with X hX
  have hcap : (∑ p ∈ Nat.primesLE ⌊X⌋₊, (1 / (p : ℝ)) * min ((N.residual X p) ^ 2) 1) ≤ M := by
    have hh := hX.1
    dsimp [cappedQuadratic] at hh
    dsimp [residual]
    linarith [sq_nonneg (N.slope X)]
  have hh := (weighted_clipped_square_bounds (Nat.primesLE ⌊X⌋₊)
    (fun p => 1 / (p : ℝ)) (N.residual X) (fun _ _ => by positivity) hK).2
  apply le_trans _ (hh.trans (mul_le_mul_of_nonneg_left hcap (sq_nonneg K)))
  unfold primeMoment
  apply sum_le_sum
  intro p hp
  rw [N.comparison_prime K X p (Nat.prime_of_mem_primesLE hp), if_pos hp, sq_abs]
  exact le_of_eq (by ring)

/-- The actual family in Section 5 satisfies the already proved Lemma 2.1. -/
theorem comparison_short_intervals (hM : Mangerel) (hE : Elliott)
    (N : NormalizedFamily f M) (K : ℝ) (hK : 1 < K) (hMpos : 0 < M) :
    Tendsto (fun H : ℕ => limsup (fun X : ℝ =>
      shortIntervalMoment H (N.comparison K X) X 2) atTop) atTop (𝓝 0) := by
  exact short_interval_second_moment_eventually hM hE (N.comparison K) K (K ^ 2 * M)
    (by linarith) (by positivity) (N.comparison_stronglyAdditive K)
    (N.comparison_coeff K (by linarith)) (N.comparison_mass K hK.le)

end NormalizedFamily

end

end Erdos1122
