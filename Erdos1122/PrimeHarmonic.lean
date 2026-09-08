import Erdos1122.PrimeTail
import Erdos1122.PrimeMoment
import Erdos1122.Constants

/-! # Explicit prime-harmonic estimates from a Mertens hypothesis -/

namespace Erdos1122

open Finset Real

noncomputable section

def primeHarmonic (y : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊y⌋₊, 1 / (p : ℝ)

/-- The precise external Mertens input. This is a proposition supplied as a
hypothesis, not an axiom or an assertion that mathlib proves Mertens' theorem. -/
def MertensBound (A B : ℝ) : Prop :=
  ∀ y : ℝ, 2 ≤ y → |primeHarmonic y - log (log y) - B| ≤ A / log y

theorem primes_restrict (X Y : ℝ) (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    (Nat.primesLE ⌊X⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ Y) = Nat.primesLE ⌊Y⌋₊ := by
  ext p
  simp only [mem_filter, Nat.mem_primesLE, Nat.le_floor_iff (hY.trans hYX), Nat.le_floor_iff hY]
  constructor
  · rintro ⟨⟨_, hp⟩, h⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨h.trans hYX, hp⟩, h⟩

theorem primeHarmonic_tail (X Y : ℝ) (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊, if Y < (p : ℝ) then 1 / (p : ℝ) else 0) =
      primeHarmonic X - primeHarmonic Y := by
  have hlow := congrArg (fun s : Finset ℕ => ∑ p ∈ s, 1 / (p : ℝ)) (primes_restrict X Y hY hYX)
  rw [sum_filter] at hlow
  unfold primeHarmonic
  rw [← hlow, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  by_cases h : (p : ℝ) ≤ Y <;> simp [h, not_lt.mpr, lt_of_not_ge]

theorem primeHarmonic_difference (A B X Y : ℝ) (hmertens : MertensBound A B)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) :
    primeHarmonic X - primeHarmonic Y ≤
      log (log X / log Y) + A / log X + A / log Y := by
  rw [log_div (ne_of_gt (log_pos (by linarith))) (ne_of_gt (log_pos (by linarith)))]
  have h₁ := (abs_le.mp (hmertens X hX)).2
  have h₂ := (abs_le.mp (hmertens Y hY)).1
  linarith

theorem normalized_log_le_iff (X p M : ℝ) (hX : 1 < X) (hp : 0 < p) :
    log p / log X ≤ M ↔ p ≤ X ^ M := by
  rw [div_le_iff₀ (log_pos hX), ← log_rpow (by linarith : 0 < X) M,
    log_le_log_iff hp (rpow_pos_of_pos (by linarith) M)]

theorem normalized_log_cross_iff (X p q : ℝ) (hX : 1 < X) (hp : 0 < p) (hq : 0 < q) :
    1 < log p / log X + log q / log X ↔ X / q < p := by
  have hlog := log_lt_log_iff (div_pos (by linarith : 0 < X) hq) hp
  rw [log_div (by linarith) hq.ne'] at hlog
  rw [← add_div, lt_div_iff₀ (log_pos hX), one_mul]
  exact (by constructor <;> intro h <;> linarith :
    log X < log p + log q ↔ log X - log q < log p).trans hlog

/-- The large-prime tail has an error tending to zero for each fixed `M`. -/
theorem primeHarmonic_large_tail (A B X M : ℝ) (hmertens : MertensBound A B)
    (hX : 2 ≤ X) (hM : 0 < M) (hM1 : M ≤ 1) (hXM : 2 ≤ X ^ M) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊, if M < log p / log X then 1 / (p : ℝ) else 0) ≤
      log (1 / M) + A / log X + A / (M * log X) := by
  have hxpos : 0 < X := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have heq : (∑ p ∈ Nat.primesLE ⌊X⌋₊,
      if M < log p / log X then 1 / (p : ℝ) else 0) =
      primeHarmonic X - primeHarmonic (X ^ M) := by
    rw [← primeHarmonic_tail X (X ^ M) (by positivity)
      (rpow_le_self_of_one_le (by linarith) hM1)]
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    have hiff := normalized_log_le_iff X p M (by linarith) hp0
    simp only [← not_le, hiff]
  rw [heq]
  have h := primeHarmonic_difference A B X (X ^ M) hmertens hX hXM
  rw [log_rpow hxpos M] at h
  have hcancel : log X / (M * log X) = 1 / M := by field_simp
  rwa [hcancel] at h

/-- Uniformity down to the smallest prime is explicit: `log q ≥ log 2`
absorbs the Mertens errors into a multiple of `log q / log X`. -/
theorem primeHarmonic_small_tail (A B X M q : ℝ) (hA : 0 ≤ A)
    (hmertens : MertensBound A B) (hX : 2 ≤ X) (hM : 0 < M)
    (hMquarter : M < 1 / 4) (hXM : 2 ≤ X ^ M)
    (hq : 2 ≤ q) (hqM : log q / log X ≤ M) :
    primeHarmonic X - primeHarmonic (X / q) ≤
      (2 + 3 * A / log 2) * (log q / log X) := by
  have hxpos : 0 < X := by linarith
  have hqpos : 0 < q := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogq : log 2 ≤ log q := log_le_log (by norm_num) hq
  have hqlog : log q ≤ M * log X := (div_le_iff₀ hlog).1 hqM
  have hscale : log 2 ≤ M * log X := by
    rw [← log_rpow hxpos M]
    exact log_le_log (by norm_num) hXM
  have hhalf : log X / 2 ≤ log (X / q) := by
    rw [log_div hxpos.ne' hqpos.ne']
    nlinarith
  have hy : 2 ≤ X / q := by
    apply (log_le_log_iff (by norm_num) (div_pos hxpos hqpos)).1
    rw [log_div hxpos.ne' hqpos.ne']
    nlinarith
  have hylog : 0 < log (X / q) := log_pos (by linarith)
  have hmain := primeHarmonic_difference A B X (X / q) hmertens hX hy
  have hratio : log X / log (X / q) = 1 / (1 - log q / log X) := by
    rw [log_div hxpos.ne' hqpos.ne']
    have hne : log X - log q ≠ 0 := by
      rw [← log_div hxpos.ne' hqpos.ne']
      exact hylog.ne'
    field_simp
  rw [hratio] at hmain
  have hsmall : 0 ≤ log q / log X := div_nonneg (hlog2.le.trans hlogq) hlog.le
  have hlogbound := log_reciprocal_one_sub_le (log q / log X) hsmall (by linarith)
  have herr : A / log (X / q) ≤ 2 * A / log X := by
    calc
      _ ≤ A / (log X / 2) := div_le_div_of_nonneg_left hA (by positivity) hhalf
      _ = _ := by ring
  have hqscaled : log 2 / log X ≤ log q / log X := div_le_div_of_nonneg_right hlogq hlog.le
  have hmul := mul_le_mul_of_nonneg_left hqscaled (show 0 ≤ 3 * A / log 2 by positivity)
  have hcancel : (3 * A / log 2) * (log 2 / log X) = 3 * A / log X := by field_simp
  rw [hcancel] at hmul
  simp only [div_eq_mul_inv] at hmain hlogbound herr hmul ⊢
  nlinarith only [hmain, hlogbound, herr, hmul]

/-- The small-prime logarithmic moment; the coefficient is independent of `M`. -/
theorem normalized_primeLogMoment_bound (X M : ℝ)
    (hX : 2 ≤ X) (hM1 : M ≤ 1) (hXM : 2 ≤ X ^ M) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊, if log p / log X ≤ M
      then (1 / (p : ℝ)) * (log p / log X) else 0) ≤
      ((log 4) * (1 + 1 / log 2)) * M := by
  have hxpos : 0 < X := by linarith
  have hlog : 0 < log X := log_pos (by linarith)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hrestrict := congrArg (fun s : Finset ℕ => ∑ p ∈ s, log p / (p : ℝ))
    (primes_restrict X (X ^ M) (by positivity) (rpow_le_self_of_one_le (by linarith) hM1))
  rw [sum_filter] at hrestrict
  have heq : (∑ p ∈ Nat.primesLE ⌊X⌋₊, if log p / log X ≤ M
      then (1 / (p : ℝ)) * (log p / log X) else 0) = primeLogMoment (X ^ M) / log X := by
    unfold primeLogMoment
    rw [← hrestrict, sum_div]
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    simp only [normalized_log_le_iff X p M (by linarith) hp0]
    split_ifs <;> ring
  rw [heq]
  have hmoment := primeLogMoment_le (X ^ M) hXM
  have hscale : log 2 ≤ log (X ^ M) := log_le_log (by norm_num) hXM
  have hratio : 1 ≤ log (X ^ M) / log 2 := (le_div_iff₀ hlog2).2 (by simpa using hscale)
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ log (4 : ℝ) from (log_pos (by norm_num)).le)
  apply (div_le_iff₀ hlog).2
  rw [log_rpow hxpos M] at hmoment hm
  simp only [div_eq_mul_inv] at hmoment hm ⊢
  nlinarith only [hmoment, hm]

def primeTailKernel (T : Finset ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ T, (1 / (p : ℝ)) *
    ∑ q ∈ Nat.primesLE ⌊X⌋₊, if X / (p : ℝ) < (q : ℝ) then 1 / (q : ℝ) else 0

theorem primeTailKernel_eq_harmonicKernel (T : Finset ℕ) (X : ℝ) (hX : 1 < X)
    (hT : T ⊆ Nat.primesLE ⌊X⌋₊) :
    primeTailKernel T X = harmonicKernel T (Nat.primesLE ⌊X⌋₊)
      (fun p => 1 / (p : ℝ)) (fun p => log p / log X) := by
  unfold primeTailKernel harmonicKernel
  apply sum_congr rfl
  intro p hp
  congr 1
  apply sum_congr rfl
  intro q hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE (hT hp)).pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primesLE hq).pos
  simp only [add_comm (log p / log X), normalized_log_cross_iff X q p hX hq0 hp0]

/-- Lemma 3.1 with explicit error and constants, conditional only on the
stated Mertens bound; Chebyshev’s inequality is proved in mathlib. -/
theorem primeTailKernel_bound (A B X M : ℝ) (T : Finset ℕ)
    (hA : 0 ≤ A) (hmertens : MertensBound A B)
    (hX : 2 ≤ X) (hM : 0 < M) (hMquarter : M < 1 / 4) (hXM : 2 ≤ X ^ M)
    (hT : T ⊆ Nat.primesLE ⌊X⌋₊) (hmass : ∑ p ∈ T, 1 / (p : ℝ) ≤ M) :
    primeTailKernel T X ≤
      M * (log (1 / M) + A / log X + A / (M * log X)) +
        (2 + 3 * A / log 2) * ((log 4) * (1 + 1 / log 2)) * M := by
  rw [primeTailKernel_eq_harmonicKernel T X (by linarith) hT]
  apply harmonicKernel_bound T (Nat.primesLE ⌊X⌋₊)
    (fun p => 1 / (p : ℝ)) (fun p => log p / log X) hT
    (fun _ _ => by positivity) M _ _ _ hM.le (by positivity) hmass
    (primeHarmonic_large_tail A B X M hmertens hX hM (by linarith) hXM) _
    (normalized_primeLogMoment_bound X M hX (by linarith) hXM)
  intro q hq hqM
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primesLE hq).two_le
  have hqpos : (0 : ℝ) < q := by linarith
  have hxpos : 0 < X := by linarith
  have heq : (∑ p ∈ Nat.primesLE ⌊X⌋₊,
      if 1 < log p / log X + log q / log X then 1 / (p : ℝ) else 0) =
      primeHarmonic X - primeHarmonic (X / q) := by
    rw [← primeHarmonic_tail X (X / q) (by positivity)
      (div_le_self hxpos.le (by linarith))]
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    simp only [normalized_log_cross_iff X p q (by linarith) hp0 hqpos]
  rw [heq]
  exact primeHarmonic_small_tail A B X M q hA hmertens hX hM hMquarter hXM hq2 hqM

/-- An explicit version of `O(M log(2/M)) + o_X(1)`. The displayed constant
depends only on the Mertens constant, and is independent of both `M` and `T`. -/
theorem primeTailKernel_bound_log (A B X M : ℝ) (T : Finset ℕ)
    (hA : 0 ≤ A) (hmertens : MertensBound A B)
    (hX : 2 ≤ X) (hM : 0 < M) (hMquarter : M < 1 / 4) (hXM : 2 ≤ X ^ M)
    (hT : T ⊆ Nat.primesLE ⌊X⌋₊) (hmass : ∑ p ∈ T, 1 / (p : ℝ) ≤ M) :
    primeTailKernel T X ≤
      (1 + (2 + 3 * A / log 2) * ((log 4) * (1 + 1 / log 2)) / log 2) *
        M * log (2 / M) + A * (M + 1) / log X := by
  have h := primeTailKernel_bound A B X M T hA hmertens hX hM hMquarter hXM hT hmass
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogX : 0 < log X := log_pos (by linarith)
  let R := (2 + 3 * A / log 2) * ((log 4) * (1 + 1 / log 2))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hratio : 2 ≤ 2 / M := (le_div_iff₀ hM).2 (by linarith)
  have hloglarge : log 2 ≤ log (2 / M) := log_le_log (by norm_num) hratio
  have hlogsmall : log (1 / M) ≤ log (2 / M) :=
    log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hM.le)
  have hmain := mul_le_mul_of_nonneg_left hlogsmall hM.le
  have hratio' : 1 ≤ log (2 / M) / log 2 := (le_div_iff₀ hlog2).2 (by simpa using hloglarge)
  have hrest := mul_le_mul_of_nonneg_left hratio' (mul_nonneg hR hM.le)
  have herr : M * (A / log X + A / (M * log X)) = A * (M + 1) / log X := by
    field_simp
  change primeTailKernel T X ≤ (1 + R / log 2) * M * log (2 / M) + A * (M + 1) / log X
  change primeTailKernel T X ≤ M * (log (1 / M) + A / log X + A / (M * log X)) + R * M at h
  rw [mul_add, mul_add] at h
  have he : M * (A / log X) + M * (A / (M * log X)) = A * (M + 1) / log X := by
    simpa only [mul_add] using herr
  simp only [div_eq_mul_inv] at h hmain he hrest ⊢
  nlinarith only [h, he, hmain, hrest]

theorem primeTailKernel_error_tendsto (A M : ℝ) :
    Filter.Tendsto (fun X : ℝ => A * (M + 1) / log X) Filter.atTop (nhds 0) :=
  tendsto_log_atTop.const_div_atTop (A * (M + 1))

/-- Uniformity over `T` is inside the eventual quantifier. `M` is fixed first. -/
theorem primeTailKernel_eventually (A B : ℝ) (hA : 0 ≤ A)
    (hmertens : MertensBound A B)
    (M : ℝ) (hM : 0 < M) (hMquarter : M < 1 / 4) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ T : Finset ℕ,
      T ⊆ Nat.primesLE ⌊X⌋₊ → (∑ p ∈ T, 1 / (p : ℝ)) ≤ M →
      primeTailKernel T X ≤
        (1 + (2 + 3 * A / log 2) * ((log 4) * (1 + 1 / log 2)) / log 2) *
          M * log (2 / M) + A * (M + 1) / log X := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop hM).eventually (Filter.eventually_ge_atTop (2 : ℝ))] with X hX hXM
  intro T hT hmass
  exact primeTailKernel_bound_log A B X M T hA hmertens hX hM hMquarter hXM hT hmass

end

end Erdos1122
