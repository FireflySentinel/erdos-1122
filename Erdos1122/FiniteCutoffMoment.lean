import Erdos1122.CenterShift
import Erdos1122.AdditiveExpansion

/-! # Finite-cutoff second moments

A coarse finite Cauchy estimate extends an eventual Turán--Kubilius upper
bound to bounded cutoffs. Its constant depends only on the cutoff, never
on the additive function. No finite-range lower estimate is used.
-/

namespace Erdos1122

open Finset Real
open Statements

set_option autoImplicit false
noncomputable section

theorem primePowerIndices_mono {X Y : ℝ} (hXY : X ≤ Y) :
    primePowerIndices X ⊆ primePowerIndices Y := by
  intro q hq
  obtain ⟨hq, hpow⟩ := mem_filter.1 hq
  obtain ⟨hp, hk⟩ := mem_product.1 hq
  refine mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, hpow.trans hXY⟩
  · exact Nat.mem_primesLE.2 ⟨(Nat.mem_primesLE.1 hp).1.trans (Nat.floor_le_floor hXY),
      (Nat.mem_primesLE.1 hp).2⟩
  · exact mem_Icc.2 ⟨(mem_Icc.1 hk).1, (mem_Icc.1 hk).2.trans (Nat.floor_le_floor hXY)⟩

theorem factorization_graph_subset_indices (n : ℕ) (X : ℝ) (hn : 0 < n) (hnX : (n : ℝ) ≤ X) :
    n.primeFactors.image (fun p => (p, n.factorization p)) ⊆ primePowerIndices X := by
  classical
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hnN : n ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ X)).2 hnX
  have hpow := Nat.ordProj_le p hn.ne'
  have hk : 0 < n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 (show p ∈ n.factorization.support from hp))
  refine mem_filter.2 ⟨mem_product.2 ⟨Nat.mem_primesLE.2 ⟨?_, hprime⟩,
    mem_Icc.2 ⟨hk, ?_⟩⟩, ?_⟩
  · exact (Nat.le_of_mem_primeFactors hp).trans hnN
  · exact (Nat.lt_pow_self hprime.one_lt).le.trans (hpow.trans hnN)
  · exact (by exact_mod_cast hpow : ((p ^ n.factorization p : ℕ) : ℝ) ≤ n).trans hnX

/-- A pointwise bound using only the prime-power expansion and Cauchy--Schwarz. -/
theorem additive_value_square_le (f : ℕ → ℝ) (hf : IsAdditive f)
    (B X : ℝ) (hX : 0 < X) (hXB : X ≤ B) (n : ℕ) (hn : 0 < n) (hnX : (n : ℝ) ≤ X) :
    (f n) ^ 2 ≤ ((⌊B⌋₊ : ℝ) * B) * primePowerMoment f X 2 := by
  classical
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul n.primeFactors
    (f := fun p => |f (p ^ n.factorization p)| ^ 2 / ((p ^ n.factorization p : ℕ) : ℝ))
    (g := fun p => ((p ^ n.factorization p : ℕ) : ℝ))
    (r := fun p => f (p ^ n.factorization p))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun p hp => by
      have hp0 : ((p ^ n.factorization p : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
      rw [sq_abs, div_mul_cancel₀ _ hp0])
  have hmass : (∑ p ∈ n.primeFactors,
      |f (p ^ n.factorization p)| ^ 2 / ((p ^ n.factorization p : ℕ) : ℝ)) ≤
      primePowerMoment f X 2 := by
    have hh := sum_le_sum_of_subset_of_nonneg (factorization_graph_subset_indices n X hn hnX)
      (f := fun q : ℕ × ℕ => |f (q.1 ^ q.2)| ^ 2 / ((q.1 ^ q.2 : ℕ) : ℝ))
      (fun _ _ _ => by positivity)
    rw [sum_image (fun _ _ _ _ h => congrArg Prod.fst h)] at hh
    exact hh
  have hcard : (n.primeFactors.card : ℝ) ≤ ⌊B⌋₊ := by
    have hin : n.primeFactors ⊆ Ioc 0 ⌊B⌋₊ := by
      intro p hp
      refine mem_Ioc.2 ⟨(Nat.prime_of_mem_primeFactors hp).pos, ?_⟩
      exact (Nat.le_of_mem_primeFactors hp).trans ((Nat.le_floor_iff (hX.le.trans hXB)).2 (hnX.trans hXB))
    exact_mod_cast (by simpa using card_le_card hin : n.primeFactors.card ≤ ⌊B⌋₊)
  have hsize : (∑ p ∈ n.primeFactors, ((p ^ n.factorization p : ℕ) : ℝ)) ≤ (⌊B⌋₊ : ℝ) * B := by
    calc
      _ ≤ ∑ _p ∈ n.primeFactors, B := by
        apply sum_le_sum
        intro p _
        exact (by exact_mod_cast Nat.ordProj_le p hn.ne' : ((p ^ n.factorization p : ℕ) : ℝ) ≤ n).trans
          (hnX.trans hXB)
      _ = (n.primeFactors.card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (hX.le.trans hXB)
  rw [← hf.factorization_sum n hn] at hc
  exact hc.trans (by
    rw [mul_comm ((⌊B⌋₊ : ℝ) * B)]
    exact mul_le_mul hmass hsize (by positivity) (by unfold primePowerMoment; positivity))

/-- The weighted center has a finite quadratic bound uniform in the function. -/
theorem weightedCenter_square_le (f : ℕ → ℝ) (B X : ℝ) (hXB : X ≤ B) :
    (weightedCenter f X) ^ 2 ≤ (primePowerIndices B).card * primePowerMoment f X 2 := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (primePowerIndices X)
    (f := fun q => |f (q.1 ^ q.2)| ^ 2 / ((q.1 ^ q.2 : ℕ) : ℝ))
    (g := fun q => (1 - 1 / (q.1 : ℝ)) ^ 2 / ((q.1 ^ q.2 : ℕ) : ℝ))
    (r := fun q => f (q.1 ^ q.2) / ((q.1 ^ q.2 : ℕ) : ℝ) * (1 - 1 / (q.1 : ℝ)))
    (fun _ _ => by positivity) (fun _ _ => by positivity) (fun q _ => by
      rw [sq_abs]
      apply le_of_eq
      ring)
  have hk : (∑ q ∈ primePowerIndices X,
      (1 - 1 / (q.1 : ℝ)) ^ 2 / ((q.1 ^ q.2 : ℕ) : ℝ)) ≤ ((primePowerIndices B).card : ℝ) := by
    calc
      _ ≤ ∑ _q ∈ primePowerIndices X, (1 : ℝ) := by
        apply sum_le_sum
        intro q hq
        have hp := Nat.prime_of_mem_primesLE (mem_product.1 (mem_filter.1 hq).1).1
        have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hp.pos
        have hp1 : (1 : ℝ) ≤ q.1 := by exact_mod_cast hp.one_le
        have hq1 : (1 : ℝ) ≤ ((q.1 ^ q.2 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero))
        have hi : 1 / (q.1 : ℝ) ≤ 1 := (div_le_one hp0).2 hp1
        have hi0 : (0 : ℝ) ≤ 1 / q.1 := by positivity
        apply (div_le_one (by linarith)).2
        nlinarith
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast card_le_card (primePowerIndices_mono hXB)
  exact hc.trans (by
    rw [mul_comm ((primePowerIndices B).card : ℝ)]
    exact mul_le_mul_of_nonneg_left hk (by positivity))

/-- A bounded interval of cutoffs costs only a constant depending on its endpoint. -/
theorem second_moment_finite_cutoff (f : ℕ → ℝ) (hf : IsAdditive f)
    (B X : ℝ) (hX : 0 < X) (hXB : X ≤ B) :
    initialMean (fun n => (f n - weightedCenter f X) ^ 2) X ≤
      (2 * ((⌊B⌋₊ : ℝ) * B + (primePowerIndices B).card)) * primePowerMoment f X 2 := by
  let C := 2 * ((⌊B⌋₊ : ℝ) * B + (primePowerIndices B).card)
  have hb : 0 ≤ primePowerMoment f X 2 := by unfold primePowerMoment; positivity
  have hB : 0 ≤ B := hX.le.trans hXB
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hh : (∑ n ∈ Ioc 0 ⌊X⌋₊, (f n - weightedCenter f X) ^ 2) ≤
      X * (C * primePowerMoment f X 2) := by
    calc
      _ ≤ ∑ _n ∈ Ioc 0 ⌊X⌋₊, C * primePowerMoment f X 2 := by
        apply sum_le_sum
        intro n hn
        have hnX := (Nat.le_floor_iff hX.le).1 (mem_Ioc.1 hn).2
        have hv := additive_value_square_le f hf B X hX hXB n (mem_Ioc.1 hn).1 hnX
        have hc := weightedCenter_square_le f B X hXB
        dsimp [C]
        nlinarith [sq_nonneg (f n + weightedCenter f X)]
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
        exact mul_le_mul_of_nonneg_right (Nat.floor_le hX.le) (mul_nonneg hC hb)
  exact (div_le_iff₀ hX).2 (by simpa only [mul_comm X] using hh)

end

end Erdos1122
