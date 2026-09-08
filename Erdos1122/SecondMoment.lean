import Erdos1122.CenterShift
import Erdos1122.AdditiveExpansion
import Erdos1122.FiniteCutoffMoment
import Erdos1122.StrongFourthMoment

/-! # Turán--Kubilius at either center, from the stated Ruzsa theorem -/

namespace Erdos1122

open Finset Real
open Statements

set_option autoImplicit false
noncomputable section

theorem initialMean_square_nonneg (g : ℕ → ℝ) (X : ℝ) :
    0 ≤ initialMean (fun n => (g n) ^ 2) X := by
  by_cases hX : 0 < X
  · exact div_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) hX.le
  · have hh : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
    simp [initialMean, hh]

/-- The coefficient zero is an admissible competitor in Ruzsa's infimum. -/
theorem ruzsaInfimum_le_second (f : ℕ → ℝ) (X : ℝ) :
    ruzsaInfimum f X ≤ primePowerMoment f X 2 := by
  have hb : BddBelow (Set.range (fun c : ℝ =>
      c ^ 2 + primePowerMoment (logarithmicResidual f c) X 2)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨c, rfl⟩
    unfold primePowerMoment
    positivity
  have hh := csInf_le hb (Set.mem_range_self (f := fun c : ℝ =>
    c ^ 2 + primePowerMoment (logarithmicResidual f c) X 2) 0)
  have he : logarithmicResidual f 0 = f := by
    funext n
    simp [logarithmicResidual]
  simpa [ruzsaInfimum, he] using hh

theorem second_moment_center_shift (f : ℕ → ℝ) (a b X : ℝ) (hX : 0 < X) :
    initialMean (fun n => (f n - a) ^ 2) X ≤
      2 * initialMean (fun n => (f n - b) ^ 2) X + 2 * (b - a) ^ 2 := by
  unfold initialMean
  apply (div_le_iff₀ hX).2
  have hh : (∑ n ∈ Ioc 0 ⌊X⌋₊, (f n - a) ^ 2) ≤
      2 * (∑ n ∈ Ioc 0 ⌊X⌋₊, (f n - b) ^ 2) + 2 * X * (b - a) ^ 2 := by
    calc
      _ ≤ ∑ n ∈ Ioc 0 ⌊X⌋₊, 2 * ((f n - b) ^ 2 + (b - a) ^ 2) := by
        apply sum_le_sum
        intro n _
        nlinarith [sq_nonneg (f n - b - (b - a))]
      _ ≤ _ := by
        simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul,
          Nat.card_Ioc, Nat.sub_zero]
        nlinarith [mul_le_mul_of_nonneg_right (Nat.floor_le hX.le) (sq_nonneg (b - a))]
  apply hh.trans_eq
  field_simp

/-- The weighted and unweighted centers give the same
Turán--Kubilius upper bound up to an absolute constant. -/
theorem ruzsa_second_moment_both_centers (hR : Ruzsa) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℝ, IsAdditive f → ∀ X : ℝ, 3 ≤ X →
      initialMean (fun n => (f n - weightedCenter f X) ^ 2) X ≤
        C * primePowerMoment f X 2 ∧
      initialMean (fun n => (f n - unweightedCenter f X) ^ 2) X ≤
        C * primePowerMoment f X 2 := by
  obtain ⟨c, C, X₀, _, hC, hX₀, hR⟩ := hR
  let B := 2 * ((⌊X₀⌋₊ : ℝ) * X₀ + (primePowerIndices X₀).card)
  let A := max C B
  have hA : 0 < A := hC.trans_le (le_max_left _ _)
  refine ⟨2 * A + 2, by positivity, ?_⟩
  intro f hf X hX
  have hn : 0 ≤ primePowerMoment f X 2 := by unfold primePowerMoment; positivity
  have hh : initialMean (fun n => (f n - weightedCenter f X) ^ 2) X ≤
      A * primePowerMoment f X 2 := by
    by_cases hlarge : X₀ ≤ X
    · have hh := (hR f hf X hlarge).2.trans
        (mul_le_mul_of_nonneg_left (ruzsaInfimum_le_second f X) hC.le)
      simp only [sq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)
    · exact (second_moment_finite_cutoff f hf X₀ X (by linarith) (le_of_not_ge hlarge)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)
  have hs := second_moment_center_shift f (unweightedCenter f X) (weightedCenter f X)
    X (by linarith)
  have he := center_shift_sq_le f X (by linarith)
  constructor <;> nlinarith

/-- The prime center error is controlled by the prime quadratic mass.
Unlike a coefficient bound, this estimate tends to zero with that mass. -/
theorem IsStronglyAdditive.prime_center_error_sq {f : ℕ → ℝ}
    (hf : IsStronglyAdditive f) (X : ℝ) (hX : 2 ≤ X) :
    (unweightedCenter f X - primeCenter f X) ^ 2 ≤ 4 * primeMoment f X 2 := by
  let e := fun p => primePowerKernel p X - 1 / (p : ℝ)
  have heq : unweightedCenter f X - primeCenter f X =
      ∑ p ∈ Nat.primesLE ⌊X⌋₊, f p * e p := by
    rw [hf.unweightedCenter_eq]
    unfold primeCenter
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    dsimp [e]
    ring
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (Nat.primesLE ⌊X⌋₊)
    (f := fun p => |f p| ^ 2 / (p : ℝ)) (g := fun p => (p : ℝ) * (e p) ^ 2)
    (r := fun p => f p * e p)
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun p hp => by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero
      rw [sq_abs]
      apply le_of_eq
      field_simp)
  have hkernel : (∑ p ∈ Nat.primesLE ⌊X⌋₊, (p : ℝ) * (e p) ^ 2) ≤ 4 := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, 4 * (1 / (p : ℝ) ^ 2) := by
        apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
        have hp0 : (0 : ℝ) < p := by linarith
        have hh := pow_le_pow_left₀ (primePowerKernel_error p X hX hp).1
          (primePowerKernel_error p X hX hp).2 2
        have hm := mul_le_mul_of_nonneg_left hh hp0.le
        change (p : ℝ) * (e p) ^ 2 ≤ _
        calc
          _ ≤ (p : ℝ) * (2 / (p : ℝ) ^ 2) ^ 2 := hm
          _ ≤ 4 * (1 / (p : ℝ) ^ 2) := by
            field_simp
            nlinarith [sq_nonneg ((p : ℝ) - 1)]
      _ = 4 * ∑ p ∈ Nat.primesLE ⌊X⌋₊, 1 / (p : ℝ) ^ 2 := (mul_sum _ _ _).symm
      _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left (prime_inverse_square_sum_le X hX) (by norm_num)
      _ = 4 := by norm_num
  rw [heq]
  exact hc.trans (by
    rw [mul_comm (4 : ℝ)]
    exact mul_le_mul_of_nonneg_left hkernel (by positivity))

/-- The strongly additive Turán--Kubilius bound at the prime center,
with no new cited input. -/
theorem stronglyAdditive_second_moment (hR : Ruzsa) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ X : ℝ, 3 ≤ X →
      initialMean (fun n => (f n - primeCenter f X) ^ 2) X ≤ C * primeMoment f X 2 := by
  obtain ⟨C, hC, hR⟩ := ruzsa_second_moment_both_centers hR
  refine ⟨4 * C + 8, by positivity, ?_⟩
  intro f hf X hX
  have hh := (hR f hf.isAdditive X hX).2
  have hp := mul_le_mul_of_nonneg_left (hf.primePowerMoment_le X 2) hC.le
  have hs := second_moment_center_shift f (primeCenter f X) (unweightedCenter f X) X (by linarith)
  have he := hf.prime_center_error_sq X (by linarith)
  nlinarith only [hh, hp, hs, he]

/-- The direct strongly additive fourth moment, retaining both prime masses. -/
theorem stronglyAdditive_fourth_moment_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ X : ℝ, 2 ≤ X →
      initialMean (fun n => (f n - primeCenter f X) ^ 4) X ≤
        C * (primeMoment f X 2 ^ 2 + primeMoment f X 4) :=
  stronglyAdditive_fourth_moment_mass_direct

/-- The two small-scale cases missing from Ruzsa's range are finite identities. -/
theorem stronglyAdditive_second_moment_small (f : ℕ → ℝ) (hf : IsStronglyAdditive f)
    (X : ℝ) (hX : 1 ≤ X) (hX3 : X < 3) :
    initialMean (fun n => (f n - primeCenter f X) ^ 2) X ≤ 2 * primeMoment f X 2 := by
  have hN1 : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).2 (by simpa using hX)
  have hN3 : ⌊X⌋₊ < 3 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast hX3)
  have hf1 := hf.isAdditive.map_one
  have hN : ⌊X⌋₊ = 1 ∨ ⌊X⌋₊ = 2 := by omega
  rcases hN with hN | hN
  · simp [initialMean, primeCenter, primeMoment, hN, hf1,
      show Nat.primesLE 1 = ∅ from rfl, show Ioc 0 1 = {1} from rfl]
  · have hX2 : 2 ≤ X := (Nat.le_floor_iff (by linarith)).1 (show (2 : ℕ) ≤ ⌊X⌋₊ by omega)
    have he : Nat.primesLE 2 = {2} := by decide
    have hi : Ioc 0 2 = ({1, 2} : Finset ℕ) := by decide
    simp only [initialMean, primeCenter, primeMoment, hN, he, hi,
      sum_singleton, sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)), hf1,
      Nat.cast_ofNat, zero_sub, neg_sq, sq_abs]
    apply (div_le_iff₀ (by linarith : 0 < X)).2
    nlinarith [mul_le_mul_of_nonneg_right hX2 (sq_nonneg (f 2))]

theorem stronglyAdditive_second_moment_all_scales (hR : Ruzsa) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ X : ℝ, 1 ≤ X →
      initialMean (fun n => (f n - primeCenter f X) ^ 2) X ≤ C * primeMoment f X 2 := by
  obtain ⟨C, hC, hR⟩ := stronglyAdditive_second_moment hR
  refine ⟨C + 2, by positivity, ?_⟩
  intro f hf X hX
  have hn : 0 ≤ primeMoment f X 2 := by unfold primeMoment; positivity
  by_cases hX3 : 3 ≤ X
  · have := hR f hf X hX3
    nlinarith
  · have := stronglyAdditive_second_moment_small f hf X hX (lt_of_not_ge hX3)
    nlinarith [mul_nonneg hC.le hn]

end

end Erdos1122
