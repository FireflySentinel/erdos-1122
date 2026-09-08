import Erdos1122.DivisorFourth

/-! # A direct fourth moment for strongly additive functions -/

namespace Erdos1122

open Finset Real
open Statements

set_option autoImplicit false
noncomputable section


def primeCutoff (X : ℝ) : Finset PrimeIndex := (Nat.primesLE ⌊X⌋₊).subtype Nat.Prime

theorem mem_primeCutoff (X : ℝ) (hX : 0 ≤ X) (p : PrimeIndex) :
    p ∈ primeCutoff X ↔ ((p : ℕ) : ℝ) ≤ X := by
  simp [primeCutoff, PrimeIndex, Nat.mem_primesLE, p.property, Nat.le_floor_iff hX]

theorem primeCutoff_mono {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    primeCutoff X ⊆ primeCutoff Y := by
  intro p hp
  exact (mem_primeCutoff Y (hX.trans hXY) p).2 (((mem_primeCutoff X hX p).1 hp).trans hXY)

theorem primeCutoff_sum (X : ℝ) (b : ℕ → ℝ) :
    (∑ p ∈ primeCutoff X, b (p : ℕ)) = ∑ p ∈ Nat.primesLE ⌊X⌋₊, b p := by
  exact sum_subtype_of_mem b (fun p hp => Nat.prime_of_mem_primesLE hp)

theorem primeCutoff_card_le (X : ℝ) : (primeCutoff X).card ≤ ⌊X⌋₊ := by
  have he : (primeCutoff X).card = (Nat.primesLE ⌊X⌋₊).card := by
    unfold primeCutoff
    rw [card_subtype, filter_true_of_mem (fun p hp => Nat.prime_of_mem_primesLE hp)]
  rw [he]
  calc
    _ ≤ (Ioc 0 ⌊X⌋₊).card := card_le_card fun p hp =>
      mem_Ioc.2 ⟨(Nat.prime_of_mem_primesLE hp).pos, (Nat.mem_primesLE.1 hp).1⟩
    _ = _ := by simp

def centeredPrimeSum (f : ℕ → ℝ) (P : Finset PrimeIndex) (n : ℕ) : ℝ :=
  ∑ p ∈ P, f (p : ℕ) * (primeIndicator p n - primeProbability p)

theorem IsStronglyAdditive.centered_eq {f : ℕ → ℝ} (hf : IsStronglyAdditive f)
    (X : ℝ) (n : ℕ) (hn : 0 < n) (hnX : n ≤ ⌊X⌋₊) :
    f n - primeCenter f X = centeredPrimeSum f (primeCutoff X) n := by
  rw [hf.eq_divisorSum X n hn hnX]
  unfold centeredPrimeSum divisorSum primeCenter primeIndicator primeProbability
  rw [primeCutoff_sum X (fun p : ℕ => f p * ((if p ∣ n then 1 else 0) - 1 / (p : ℝ))), ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem primeCutoff_second (f : ℕ → ℝ) (X : ℝ) :
    (∑ p ∈ primeCutoff X, f (p : ℕ) ^ 2 * primeProbability p) = primeMoment f X 2 := by
  simp only [primeProbability, mul_one_div, primeMoment, sq_abs]
  exact primeCutoff_sum X (fun p : ℕ => f p ^ 2 / (p : ℝ))

theorem prime_large_divisor_card (P : Finset PrimeIndex) (n : ℕ) (hn : 0 < n)
    (X Y : ℝ) (hY : 1 < Y) (hnX : (n : ℝ) ≤ X) (hXY : X ≤ Y ^ 4)
    (hP : ∀ p ∈ P, Y ≤ ((p : ℕ) : ℝ)) :
    (P.filter (fun p : PrimeIndex => (p : ℕ) ∣ n)).card ≤ 4 := by
  let S := P.filter (fun p : PrimeIndex => (p : ℕ) ∣ n)
  have hd : (∏ p ∈ S, (p : ℕ)) ∣ n :=
    (prime_prod_dvd_iff S n).2 (fun p hp => (mem_filter.1 hp).2)
  have hprod : Y ^ S.card ≤ ((∏ p ∈ S, (p : ℕ) : ℕ) : ℝ) := by
    rw [Nat.cast_prod, ← prod_const]
    exact prod_le_prod (fun _ _ => by linarith) (fun p hp => hP p (mem_filter.1 hp).1)
  have hpn : ((∏ p ∈ S, (p : ℕ) : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd hn hd
  exact (pow_le_pow_iff_right₀ hY).1 (hprod.trans (hpn.trans (hnX.trans hXY)))

theorem initialMean_mono (f g : ℕ → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (hfg : ∀ n ∈ Ioc 0 ⌊X⌋₊, f n ≤ g n) : initialMean f X ≤ initialMean g X :=
  div_le_div_of_nonneg_right (sum_le_sum hfg) hX

theorem initialMean_add (f g : ℕ → ℝ) (X : ℝ) :
    initialMean (fun n => f n + g n) X = initialMean f X + initialMean g X := by
  simp [initialMean, sum_add_distrib, add_div]

theorem initialMean_const_le (B X : ℝ) (hB : 0 ≤ B) (hX : 0 < X) :
    initialMean (fun _ => B) X ≤ B := by
  unfold initialMean
  simp only [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
  apply (div_le_iff₀ hX).2
  nlinarith [mul_le_mul_of_nonneg_right (Nat.floor_le hX.le) hB]

theorem primeCutoff_fourth (f : ℕ → ℝ) (X : ℝ) :
    (∑ p ∈ primeCutoff X, f (p : ℕ) ^ 4 * primeProbability p) = primeMoment f X 4 := by
  simp only [primeProbability, mul_one_div, primeMoment, abs_pow_four]
  exact primeCutoff_sum X (fun p : ℕ => f p ^ 4 / (p : ℝ))

theorem primeMoment_nonneg (f : ℕ → ℝ) (X : ℝ) (j : ℕ) : 0 ≤ primeMoment f X j := by
  unfold primeMoment
  positivity

theorem primeMoment_mono (f : ℕ → ℝ) (j : ℕ) {X Y : ℝ} (hXY : X ≤ Y) :
    primeMoment f X j ≤ primeMoment f Y j := by
  unfold primeMoment
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.2 ⟨(Nat.mem_primesLE.1 hp).1.trans (Nat.floor_le_floor hXY),
      (Nat.mem_primesLE.1 hp).2⟩
  · intro _ _ _
    positivity

theorem centeredPrimeSum_abs_le_sum (f : ℕ → ℝ) (P : Finset PrimeIndex) (n : ℕ) :
    |centeredPrimeSum f P n| ≤ ∑ p ∈ P, |f (p : ℕ)| := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p _
  rw [abs_mul]
  have hq := primeProbability_bounds p
  have hb : |primeIndicator p n - primeProbability p| ≤ 1 := by
    unfold primeIndicator
    split_ifs <;> exact abs_le.2 ⟨by linarith [hq.1, hq.2], by linarith [hq.1, hq.2]⟩
  simpa using mul_le_mul_of_nonneg_left hb (abs_nonneg (f (p : ℕ)))

theorem primeCutoff_abs_sum_sq (f : ℕ → ℝ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ p ∈ primeCutoff Y, |f (p : ℕ)|) ^ 2 ≤ primeMoment f Y 2 * Y ^ 2 := by
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (primeCutoff Y)
    (f := fun p => f (p : ℕ) ^ 2 * primeProbability p)
    (g := fun p => ((p : ℕ) : ℝ)) (r := fun p => |f (p : ℕ)|)
    (fun p _ => mul_nonneg (sq_nonneg _) (primeProbability_bounds p).1)
    (fun _ _ => by positivity) (fun p _ => by
      have hp : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
      simp only [sq_abs, primeProbability]
      field_simp
      rfl)
  rw [primeCutoff_second] at hc
  have hsize : (∑ p ∈ primeCutoff Y, ((p : ℕ) : ℝ)) ≤ Y ^ 2 := by
    calc
      _ ≤ ∑ _p ∈ primeCutoff Y, Y := sum_le_sum fun p hp => (mem_primeCutoff Y hY p).1 hp
      _ = ((primeCutoff Y).card : ℝ) * Y := by simp
      _ ≤ Y * Y := mul_le_mul_of_nonneg_right
        ((show ((primeCutoff Y).card : ℝ) ≤ ⌊Y⌋₊ from by exact_mod_cast primeCutoff_card_le Y).trans
          (Nat.floor_le hY)) hY
      _ = _ := by ring
  exact hc.trans (mul_le_mul_of_nonneg_left hsize (primeMoment_nonneg f Y 2))

theorem small_prime_fourth (f : ℕ → ℝ) (X Y : ℝ)
    (hX : 0 < X) (hY : 0 ≤ Y) (hXY : X = Y ^ 4) :
    initialMean (fun n => centeredPrimeSum f (primeCutoff Y) n ^ 4) X ≤
      primeMoment f Y 4 + 19 * primeMoment f Y 2 ^ 2 := by
  have hp := pow_le_pow_left₀ (sq_nonneg (∑ p ∈ primeCutoff Y, |f (p : ℕ)|))
    (primeCutoff_abs_sum_sq f Y hY) 2
  have herr : (16 / X) * (∑ p ∈ primeCutoff Y, |f (p : ℕ)|) ^ 4 ≤
      16 * primeMoment f Y 2 ^ 2 := by
    calc
      _ ≤ (16 / X) * (primeMoment f Y 2 * Y ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [← pow_mul] using hp
      _ = _ := by
        rw [mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, ← hXY]
        field_simp
  have hh := divisor_fourth_moment (primeCutoff Y) (fun p => f (p : ℕ)) X hX
  rw [primeCutoff_second, primeCutoff_fourth] at hh
  change initialMean (fun n => (∑ p ∈ primeCutoff Y,
    f (p : ℕ) * (primeIndicator p n - primeProbability p)) ^ 4) X ≤ _
  linarith

def primeFourthTailWeight : ℝ := log 4 * (log 4 + 1 / log 2)

theorem primeFourthTailWeight_nonneg : 0 ≤ primeFourthTailWeight := by
  unfold primeFourthTailWeight
  positivity

theorem fourth_tail_reciprocal (X Y : ℝ) (hY : 2 ≤ Y) (hYX : Y ≤ X) (hXY : X = Y ^ 4) :
    (∑ p ∈ primeCutoff X \ primeCutoff Y, primeProbability p) ≤ primeFourthTailWeight := by
  rw [sum_sdiff_eq_sub (primeCutoff_mono (by linarith) hYX)]
  simp only [primeProbability]
  rw [primeCutoff_sum X (fun p : ℕ => 1 / (p : ℝ)), primeCutoff_sum Y (fun p : ℕ => 1 / (p : ℝ))]
  change primeHarmonic X - primeHarmonic Y ≤ _
  have hl : log Y ≠ 0 := (log_pos (by linarith)).ne'
  have hratio : log X / log Y = 4 := by rw [hXY, log_pow]; field_simp; norm_num
  have hh := primeHarmonic_difference X Y hY hYX
  rw [hratio] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (one_div_le_one_div_of_le (log_pos (by norm_num))
    (log_le_log (by norm_num) hY))

theorem sum_fourth_le_card_cube {ι : Type*} (P : Finset ι) (a : ι → ℝ) :
    (∑ p ∈ P, a p) ^ 4 ≤ (P.card : ℝ) ^ 3 * ∑ p ∈ P, a p ^ 4 := by
  have h₂ := square_sum_le_card_sum_square P a
  have h₄ := square_sum_le_card_sum_square P (fun p => a p ^ 2)
  simp only [← pow_mul, show 2 * 2 = 4 from rfl] at h₄
  have hs := pow_le_pow_left₀ (sq_nonneg (∑ p ∈ P, a p)) h₂ 2
  have hm := mul_le_mul_of_nonneg_left h₄ (sq_nonneg (P.card : ℝ))
  nlinarith only [hs, hm]

theorem primeIndicator_mean_le (p : PrimeIndex) (X : ℝ) (hX : 0 < X) :
    initialMean (primeIndicator p) X ≤ primeProbability p := by
  unfold initialMean primeIndicator primeProbability
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.Ioc_filter_dvd_card_eq_div]
  have hh : ((⌊X⌋₊ / (p : ℕ) : ℕ) : ℝ) ≤ X / ((p : ℕ) : ℝ) :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right (Nat.floor_le hX.le) (by positivity))
  apply (div_le_iff₀ hX).2
  simpa [div_eq_mul_inv, mul_comm] using hh

theorem large_prime_raw_fourth (f : ℕ → ℝ) (X Y : ℝ) (hY : 2 ≤ Y)
    (hYX : Y ≤ X) (hXY : X = Y ^ 4) :
    initialMean (fun n => (∑ p ∈ primeCutoff X \ primeCutoff Y,
      f (p : ℕ) * primeIndicator p n) ^ 4) X ≤ 64 * primeMoment f X 4 := by
  let P := primeCutoff X \ primeCutoff Y
  have hX : 0 < X := by linarith
  have hb : initialMean (fun n => (∑ p ∈ P, f (p : ℕ) * primeIndicator p n) ^ 4) X ≤
      initialMean (fun n => 64 * ∑ p ∈ P, f (p : ℕ) ^ 4 * primeIndicator p n) X := by
    apply initialMean_mono _ _ X hX.le
    intro n hn
    let S := P.filter (fun p : PrimeIndex => (p : ℕ) ∣ n)
    have hc : S.card ≤ 4 := prime_large_divisor_card P n (mem_Ioc.1 hn).1 X Y (by linarith)
      ((show (n : ℝ) ≤ ⌊X⌋₊ from by exact_mod_cast (mem_Ioc.1 hn).2).trans (Nat.floor_le hX.le))
      hXY.le (fun p hp => (lt_of_not_ge (fun hh => (mem_sdiff.1 hp).2
        ((mem_primeCutoff Y (by linarith) p).2 hh))).le)
    have he (a : ℕ → ℝ) : (∑ p ∈ P, a (p : ℕ) * primeIndicator p n) = ∑ p ∈ S, a (p : ℕ) := by
      simp [S, primeIndicator, sum_filter]
    rw [he f, he (fun p => f p ^ 4)]
    apply (sum_fourth_le_card_cube S (fun p => f (p : ℕ))).trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => by positivity)
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ S.card)
      (show (S.card : ℝ) ≤ 4 from by exact_mod_cast hc) 3
    norm_num at hh ⊢
    exact hh
  rw [initialMean_const_mul, initialMean_finset_sum] at hb
  simp_rw [initialMean_const_mul] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ p ∈ P, f (p : ℕ) ^ 4 * primeProbability p := sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (primeIndicator_mean_le p X hX) (by positivity)
    _ ≤ ∑ p ∈ primeCutoff X, f (p : ℕ) ^ 4 * primeProbability p :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ =>
        mul_nonneg (by positivity) (primeProbability_bounds p).1)
    _ = _ := primeCutoff_fourth f X

theorem large_prime_center_fourth (f : ℕ → ℝ) (X Y : ℝ) (hY : 2 ≤ Y)
    (hYX : Y ≤ X) (hXY : X = Y ^ 4) :
    (∑ p ∈ primeCutoff X \ primeCutoff Y, f (p : ℕ) * primeProbability p) ^ 4 ≤
      primeMoment f X 2 ^ 2 * primeFourthTailWeight ^ 2 := by
  let P := primeCutoff X \ primeCutoff Y
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul P
    (f := fun p => f (p : ℕ) ^ 2 * primeProbability p)
    (g := primeProbability) (r := fun p => f (p : ℕ) * primeProbability p)
    (fun p _ => mul_nonneg (sq_nonneg _) (primeProbability_bounds p).1)
    (fun p _ => (primeProbability_bounds p).1) (fun _ _ => le_of_eq (by ring))
  have hm : (∑ p ∈ P, f (p : ℕ) ^ 2 * primeProbability p) ≤ primeMoment f X 2 := by
    rw [← primeCutoff_second]
    exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ =>
      mul_nonneg (sq_nonneg _) (primeProbability_bounds p).1)
  have hsq := hc.trans (mul_le_mul hm (fourth_tail_reciprocal X Y hY hYX hXY)
    (sum_nonneg fun p _ => (primeProbability_bounds p).1) (primeMoment_nonneg f X 2))
  have hh := pow_le_pow_left₀ (sq_nonneg _) hsq 2
  simpa only [mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl] using hh

theorem initialMean_fourth_add (f g : ℕ → ℝ) (X : ℝ) (hX : 0 ≤ X) :
    initialMean (fun n => (f n + g n) ^ 4) X ≤
      8 * (initialMean (fun n => f n ^ 4) X + initialMean (fun n => g n ^ 4) X) := by
  have hh := initialMean_mono _ _ X hX
    (fun n (_ : n ∈ Ioc 0 ⌊X⌋₊) => two_term_fourth_le (f n) (g n))
  simpa only [initialMean_const_mul, initialMean_add] using hh

theorem large_prime_fourth (f : ℕ → ℝ) (X Y : ℝ) (hY : 2 ≤ Y)
    (hYX : Y ≤ X) (hXY : X = Y ^ 4) :
    initialMean (fun n => centeredPrimeSum f (primeCutoff X \ primeCutoff Y) n ^ 4) X ≤
      8 * (64 * primeMoment f X 4 + primeMoment f X 2 ^ 2 * primeFourthTailWeight ^ 2) := by
  let P := primeCutoff X \ primeCutoff Y
  let c := ∑ p ∈ P, f (p : ℕ) * primeProbability p
  have hX : 0 < X := by linarith
  have he : centeredPrimeSum f P =
      (fun n => (∑ p ∈ P, f (p : ℕ) * primeIndicator p n) + -c) := by
    funext n
    unfold centeredPrimeSum
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    rfl
  change initialMean (fun n => centeredPrimeSum f P n ^ 4) X ≤ _
  rw [he]
  have hh := initialMean_fourth_add (fun n => ∑ p ∈ P, f (p : ℕ) * primeIndicator p n)
    (fun _ => -c) X hX.le
  have hc := initialMean_const_le (c ^ 4) X (by positivity) hX
  have hr := large_prime_raw_fourth f X Y hY hYX hXY
  have hm := large_prime_center_fourth f X Y hY hYX hXY
  have hneg : (-c) ^ 4 = c ^ 4 := by ring
  simp only [hneg] at hh
  change c ^ 4 ≤ _ at hm
  dsimp only [P] at hh
  linarith

/-- A direct fourth-moment inequality for every real strongly additive function. -/
theorem stronglyAdditive_fourth_moment_mass_direct :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ X : ℝ, 2 ≤ X →
      initialMean (fun n => (f n - primeCenter f X) ^ 4) X ≤
        C * (primeMoment f X 2 ^ 2 + primeMoment f X 4) := by
  let C : ℝ := 70000 + 64 * primeFourthTailWeight ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf X hX
  have hX0 : 0 < X := by linarith
  have hQ := primeMoment_nonneg f X 4
  have he : initialMean (fun n => (f n - primeCenter f X) ^ 4) X =
      initialMean (fun n => centeredPrimeSum f (primeCutoff X) n ^ 4) X := by
    unfold initialMean
    congr 1
    apply sum_congr rfl
    intro n hn
    exact congrArg (fun t : ℝ => t ^ 4) (hf.centered_eq X n (mem_Ioc.1 hn).1 (mem_Ioc.1 hn).2)
  rw [he]
  by_cases hsmall : X < 16
  · have hb : initialMean (fun n => centeredPrimeSum f (primeCutoff X) n ^ 4) X ≤
        65536 * primeMoment f X 2 ^ 2 := by
      apply le_trans _ (initialMean_const_le _ X (by positivity) hX0)
      apply initialMean_mono _ _ X hX0.le
      intro n _
      have h₁ := pow_le_pow_left₀ (abs_nonneg _)
        (centeredPrimeSum_abs_le_sum f (primeCutoff X) n) 4
      have h₂ := pow_le_pow_left₀ (sq_nonneg _) (primeCutoff_abs_sum_sq f X hX0.le) 2
      have h₃ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hX0.le hsmall.le 4) (sq_nonneg (primeMoment f X 2))
      simp only [abs_pow_four] at h₁
      norm_num at h₃
      nlinarith only [h₁, h₂, h₃]
    have hcoef : 65536 ≤ C := by dsimp [C]; nlinarith [sq_nonneg primeFourthTailWeight]
    have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (primeMoment f X 2))
    nlinarith only [hb, hm, mul_nonneg hC.le hQ]
  · have hX16 : 16 ≤ X := le_of_not_gt hsmall
    let Y := sqrt (sqrt X)
    have hY0 : 0 ≤ Y := sqrt_nonneg _
    have hY4 : Y ^ 4 = X := by
      calc
        _ = (Y ^ 2) ^ 2 := by ring
        _ = (sqrt X) ^ 2 := by rw [show Y ^ 2 = sqrt X from sq_sqrt (sqrt_nonneg X)]
        _ = X := sq_sqrt hX0.le
    have hY : 2 ≤ Y := by
      by_contra hh
      have hp := pow_lt_pow_left₀ (lt_of_not_ge hh) hY0 (by decide : 4 ≠ 0)
      norm_num at hp
      linarith
    have hYX : Y ≤ X := by
      rw [← hY4]
      exact le_self_pow₀ (by linarith) (by decide)
    have hsub := primeCutoff_mono hY0 hYX
    have hs₀ := small_prime_fourth f X Y hX0 hY0 hY4.symm
    have hs : initialMean (fun n => centeredPrimeSum f (primeCutoff Y) n ^ 4) X ≤
        primeMoment f X 4 + 19 * primeMoment f X 2 ^ 2 := by
      have h₂ := pow_le_pow_left₀ (primeMoment_nonneg f Y 2) (primeMoment_mono f 2 hYX) 2
      have h₄ := primeMoment_mono f 4 hYX
      linarith
    have hl := large_prime_fourth f X Y hY hYX hY4.symm
    have hsplit (n : ℕ) : centeredPrimeSum f (primeCutoff X) n =
        centeredPrimeSum f (primeCutoff Y) n +
          centeredPrimeSum f (primeCutoff X \ primeCutoff Y) n := by
      unfold centeredPrimeSum
      rw [sum_sdiff_eq_sub hsub]
      ring
    have hh := initialMean_fourth_add (centeredPrimeSum f (primeCutoff Y))
      (centeredPrimeSum f (primeCutoff X \ primeCutoff Y)) X hX0.le
    simp_rw [← hsplit] at hh
    have hb : initialMean (fun n => centeredPrimeSum f (primeCutoff X) n ^ 4) X ≤
        4104 * primeMoment f X 4 + (152 + 64 * primeFourthTailWeight ^ 2) * primeMoment f X 2 ^ 2 := by
      nlinarith only [hh, hs, hl]
    have hcoef₁ : 4104 ≤ C := by dsimp [C]; nlinarith [sq_nonneg primeFourthTailWeight]
    have hcoef₂ : 152 + 64 * primeFourthTailWeight ^ 2 ≤ C := by dsimp [C]; linarith
    have hm₁ := mul_le_mul_of_nonneg_right hcoef₁ hQ
    have hm₂ := mul_le_mul_of_nonneg_right hcoef₂ (sq_nonneg (primeMoment f X 2))
    nlinarith only [hb, hm₁, hm₂]

/-- The uniform form used by the short-interval argument. -/
theorem stronglyAdditive_fourth_moment (L V : ℝ) (_hL : 0 ≤ L) (hV : 0 ≤ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℕ → ℝ, IsStronglyAdditive f → ∀ X : ℝ, 2 ≤ X →
      (∀ p ∈ Nat.primesLE ⌊X⌋₊, |f p| ≤ L) → primeMoment f X 2 ≤ V →
      initialMean (fun n => (f n - primeCenter f X) ^ 4) X ≤ C := by
  obtain ⟨A, hA, hmoment⟩ := stronglyAdditive_fourth_moment_mass_direct
  refine ⟨A * (V ^ 2 + L ^ 2 * V), by positivity, ?_⟩
  intro f hf X hX hcoeff hmass
  have h₂ := pow_le_pow_left₀ (primeMoment_nonneg f X 2) hmass 2
  have h₄ := (primeMoment_fourth_le f X L hcoeff).trans
    (mul_le_mul_of_nonneg_left hmass (sq_nonneg L))
  exact (hmoment f hf X hX).trans (mul_le_mul_of_nonneg_left (add_le_add h₂ h₄) hA.le)


end

end Erdos1122
