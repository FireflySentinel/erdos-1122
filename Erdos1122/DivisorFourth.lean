import Erdos1122.BernoulliFourth
import Mathlib.Data.Nat.GCD.BigOperators

/-! # Comparing divisor moments with finite Bernoulli moments -/

namespace Erdos1122

open Finset
open Statements

set_option autoImplicit false
noncomputable section

/-- Prime numbers, with a reducible subtype for finite sums. -/
abbrev PrimeIndex := {p : ℕ // p.Prime}

def primeProbability (p : PrimeIndex) : ℝ := 1 / ((p : ℕ) : ℝ)

def primeIndicator (p : PrimeIndex) (n : ℕ) : ℝ := if (p : ℕ) ∣ n then 1 else 0

def divisorMonomial (s : Finset PrimeIndex) (n : ℕ) : ℝ := ∏ p ∈ s, primeIndicator p n

theorem primeProbability_bounds (p : PrimeIndex) :
    0 ≤ primeProbability p ∧ primeProbability p ≤ 1 := by
  have hp : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.one_lt.le
  unfold primeProbability
  constructor
  · positivity
  · exact (div_le_one (by linarith)).2 hp

theorem prime_prod_dvd_iff (s : Finset PrimeIndex) (n : ℕ) :
    (∏ p ∈ s, (p : ℕ)) ∣ n ↔ ∀ p ∈ s, (p : ℕ) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hc : Nat.Coprime (p : ℕ) (∏ q ∈ s, (q : ℕ)) := by
      apply Nat.coprime_prod_right_iff.2
      intro q hq
      apply (Nat.coprime_primes p.property q.property).2
      intro he
      exact hps ((Subtype.coe_injective he) ▸ hq)
    rw [prod_insert hps]
    constructor
    · intro h
      have h₁ := dvd_of_mul_right_dvd h
      have h₂ := ih.1 (dvd_of_mul_left_dvd h)
      simpa using (show (p : ℕ) ∣ n ∧ ∀ q ∈ s, (q : ℕ) ∣ n from ⟨h₁, h₂⟩)
    · intro h
      exact hc.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self _ _))
        (ih.2 (fun q hq => h q (mem_insert_of_mem hq)))

theorem divisorMonomial_eq (s : Finset PrimeIndex) (n : ℕ) :
    divisorMonomial s n = if (∏ p ∈ s, (p : ℕ)) ∣ n then 1 else 0 := by
  simp only [prime_prod_dvd_iff]
  unfold divisorMonomial primeIndicator
  by_cases h : ∀ p ∈ s, (p : ℕ) ∣ n
  · rw [if_pos h]
    exact prod_eq_one fun p hp => if_pos (h p hp)
  · obtain ⟨p, hp⟩ := not_forall.1 h
    obtain ⟨hps, hpn⟩ := Classical.not_imp.1 hp
    have he : (∏ p ∈ s, if (p : ℕ) ∣ n then (1 : ℝ) else 0) = 0 :=
      prod_eq_zero hps (if_neg hpn)
    rw [if_neg h, he]

theorem divisorMonomial_insert (p : PrimeIndex) (s : Finset PrimeIndex) (n : ℕ) :
    divisorMonomial (insert p s) n = primeIndicator p n * divisorMonomial s n := by
  simp only [divisorMonomial_eq, prime_prod_dvd_iff, forall_mem_insert, primeIndicator]
  split_ifs <;> simp_all

theorem divisor_monomial_error (X : ℝ) (hX : 0 < X) (s : Finset PrimeIndex) :
    |initialMean (divisorMonomial s) X - bernoulliMonomial primeProbability s| ≤ 1 / X := by
  let d : ℕ := ∏ p ∈ s, (p : ℕ)
  have hd : 0 < d := prod_pos (fun p _ => p.property.pos)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hm : bernoulliMonomial primeProbability s = 1 / (d : ℝ) := by
    simp [bernoulliMonomial, primeProbability, d, Nat.cast_prod]
  have he : initialMean (divisorMonomial s) X = (⌊X / (d : ℝ)⌋₊ : ℝ) / X := by
    unfold initialMean
    simp_rw [divisorMonomial_eq]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.Ioc_filter_dvd_card_eq_div]
    rw [Nat.floor_div_natCast]
  rw [hm, he]
  have hf₁ := Nat.floor_le (show 0 ≤ X / (d : ℝ) by positivity)
  have hf₂ := Nat.lt_floor_add_one (X / (d : ℝ))
  have he' : (⌊X / (d : ℝ)⌋₊ : ℝ) / X - 1 / (d : ℝ) =
      ((⌊X / (d : ℝ)⌋₊ : ℝ) - X / (d : ℝ)) / X := by field_simp
  rw [he', abs_div, abs_of_pos hX]
  exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hX.le

theorem centerOp_divisor_mean (X : ℝ) (g : ℕ → ℝ) (p : PrimeIndex) :
    centerOp primeProbability p
      (fun t => initialMean (fun n => g n * divisorMonomial t n) X) =
    (fun s => initialMean (fun n => g n * (primeIndicator p n - primeProbability p) *
      divisorMonomial s n) X) := by
  funext s
  unfold centerOp initialMean
  simp_rw [divisorMonomial_insert]
  rw [← mul_div_assoc, mul_sum, ← sub_div, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  ring

theorem divisor_four_correlation_error (X : ℝ) (hX : 0 < X) (i j k l : PrimeIndex) :
    |initialMean (fun n => (primeIndicator i n - primeProbability i) *
        (primeIndicator j n - primeProbability j) *
        (primeIndicator k n - primeProbability k) *
        (primeIndicator l n - primeProbability l)) X -
      bernoulliCorrelation primeProbability i j k l| ≤ 16 / X := by
  have he := four_centerOp_error primeProbability i j k l
    (fun s => initialMean (divisorMonomial s) X) (bernoulliMonomial primeProbability) (1 / X)
    (fun p => by rw [abs_of_nonneg (primeProbability_bounds p).1]; exact (primeProbability_bounds p).2)
    (divisor_monomial_error X hX)
  have hid : (fun s => initialMean (divisorMonomial s) X) =
      (fun s => initialMean (fun n => (1 : ℝ) * divisorMonomial s n) X) := by simp
  rw [hid] at he
  simp_rw [centerOp_divisor_mean] at he
  simpa [divisorMonomial, bernoulliCorrelation, mul_comm, mul_left_comm, mul_assoc,
    div_eq_mul_inv] using he

theorem initialMean_finset_sum {ι : Type*} (P : Finset ι) (F : ι → ℕ → ℝ) (X : ℝ) :
    initialMean (fun n => ∑ p ∈ P, F p n) X = ∑ p ∈ P, initialMean (F p) X := by
  unfold initialMean
  rw [sum_comm, sum_div]

theorem initialMean_const_mul (F : ℕ → ℝ) (c X : ℝ) :
    initialMean (fun n => c * F n) X = c * initialMean F X := by
  simp only [initialMean, ← mul_sum, mul_div_assoc]

/-- A finite arithmetic fourth-moment bound with its complete floor error. -/
theorem divisor_fourth_moment (P : Finset PrimeIndex) (a : PrimeIndex → ℝ)
    (X : ℝ) (hX : 0 < X) :
    initialMean (fun n => (∑ p ∈ P, a p * (primeIndicator p n - primeProbability p)) ^ 4) X ≤
      (∑ p ∈ P, a p ^ 4 * primeProbability p) +
        3 * (∑ p ∈ P, a p ^ 2 * primeProbability p) ^ 2 +
        (16 / X) * (∑ p ∈ P, |a p|) ^ 4 := by
  let b : PrimeIndex → ℕ → ℝ := fun p n => primeIndicator p n - primeProbability p
  have hterm (i j k l : PrimeIndex) :
      initialMean (fun n => a i * b i n * (a j * b j n) * (a k * b k n) * (a l * b l n)) X ≤
      a i * a j * a k * a l * bernoulliCorrelation primeProbability i j k l +
        (16 / X) * (|a i| * |a j| * |a k| * |a l|) := by
    have hh := mul_le_mul_of_nonneg_left (divisor_four_correlation_error X hX i j k l)
      (abs_nonneg (a i * a j * a k * a l))
    have hid : (fun n => a i * b i n * (a j * b j n) * (a k * b k n) * (a l * b l n)) =
        (fun n => (a i * a j * a k * a l) * (b i n * b j n * b k n * b l n)) := by
      funext n
      ring
    rw [hid, initialMean_const_mul]
    rw [← abs_mul] at hh
    have hh' := (abs_le.1 hh).2
    simp only [abs_mul] at hh'
    dsimp only [b]
    nlinarith only [hh']
  calc
    _ = ∑ i ∈ P, ∑ j ∈ P, ∑ k ∈ P, ∑ l ∈ P,
        initialMean (fun n => a i * b i n * (a j * b j n) * (a k * b k n) * (a l * b l n)) X := by
      simp_rw [sum_fourth_expand, initialMean_finset_sum]
      rfl
    _ ≤ ∑ i ∈ P, ∑ j ∈ P, ∑ k ∈ P, ∑ l ∈ P,
        (a i * a j * a k * a l * bernoulliCorrelation primeProbability i j k l +
          (16 / X) * (|a i| * |a j| * |a k| * |a l|)) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ =>
        sum_le_sum fun l _ => hterm i j k l
    _ = (∑ i ∈ P, ∑ j ∈ P, ∑ k ∈ P, ∑ l ∈ P,
        a i * a j * a k * a l * bernoulliCorrelation primeProbability i j k l) +
        (16 / X) * (∑ p ∈ P, |a p|) ^ 4 := by
      simp_rw [sum_add_distrib]
      simp only [← sum_mul, ← mul_sum]
      ring
    _ ≤ _ := add_le_add (bernoulli_fourth_sum_le P primeProbability a primeProbability_bounds) le_rfl

end

end Erdos1122
