import Erdos1122.PrimeTail
import Erdos1122.PrimeReciprocal
import Erdos1122.Constants

/-! # Unconditional prime-harmonic estimates -/

namespace Erdos1122

open Finset Real

noncomputable section

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
theorem primeHarmonic_large_tail (X M : ℝ)
    (hX : 2 ≤ X) (hM : 0 < M) (hM1 : M ≤ 1) (hXM : 2 ≤ X ^ M) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊, if M < log p / log X then 1 / (p : ℝ) else 0) ≤
      log 4 * log (1 / M) + log 4 / (M * log X) := by
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
  have h := primeHarmonic_difference X (X ^ M) hXM
    (rpow_le_self_of_one_le (by linarith) hM1)
  rw [log_rpow hxpos M] at h
  have hcancel : log X / (M * log X) = 1 / M := by field_simp
  simpa [hcancel, mul_add, div_eq_mul_inv] using h

/-- Uniformity down to the smallest prime is explicit: `log q ≥ log 2`
absorbs the endpoint error into a multiple of `log q / log X`. -/
theorem primeHarmonic_small_tail (X M q : ℝ) (hX : 2 ≤ X) (hM : 0 < M)
    (hMquarter : M < 1 / 4) (hXM : 2 ≤ X ^ M)
    (hq : 2 ≤ q) (hqM : log q / log X ≤ M) :
    primeHarmonic X - primeHarmonic (X / q) ≤
      (2 * log 4 + 2 * log 4 / log 2) * (log q / log X) := by
  have hD : 0 ≤ log (4 : ℝ) := (log_pos (by norm_num)).le
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
  have hmain := primeHarmonic_difference X (X / q) hy (div_le_self hxpos.le (by linarith))
  have hratio : log X / log (X / q) = 1 / (1 - log q / log X) := by
    rw [log_div hxpos.ne' hqpos.ne']
    have hne : log X - log q ≠ 0 := by
      rw [← log_div hxpos.ne' hqpos.ne']
      exact hylog.ne'
    field_simp
  rw [hratio] at hmain
  have hsmall : 0 ≤ log q / log X := div_nonneg (hlog2.le.trans hlogq) hlog.le
  have hlogbound := log_reciprocal_one_sub_le (log q / log X) hsmall (by linarith)
  have hlogmul := mul_le_mul_of_nonneg_left hlogbound hD
  have herr : log 4 / log (X / q) ≤ 2 * log 4 / log X := by
    calc
      _ ≤ log 4 / (log X / 2) := div_le_div_of_nonneg_left hD (by positivity) hhalf
      _ = _ := by ring
  have hqscaled : log 2 / log X ≤ log q / log X := div_le_div_of_nonneg_right hlogq hlog.le
  have hmul := mul_le_mul_of_nonneg_left hqscaled (show 0 ≤ 2 * log 4 / log 2 by positivity)
  have hcancel : (2 * log 4 / log 2) * (log 2 / log X) = 2 * log 4 / log X := by field_simp
  rw [hcancel] at hmul
  simp only [div_eq_mul_inv] at hmain hlogmul herr hmul ⊢
  nlinarith only [hmain, hlogmul, herr, hmul]

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

/-- Lemma 3.1 from Chebyshev and Abel summation, with no external input. -/
theorem primeTailKernel_bound (X M : ℝ) (T : Finset ℕ)
    (hX : 2 ≤ X) (hM : 0 < M) (hMquarter : M < 1 / 4) (hXM : 2 ≤ X ^ M)
    (hT : T ⊆ Nat.primesLE ⌊X⌋₊) (hmass : ∑ p ∈ T, 1 / (p : ℝ) ≤ M) :
    primeTailKernel T X ≤
      M * (log 4 * log (1 / M) + log 4 / (M * log X)) +
        (2 * log 4 + 2 * log 4 / log 2) * ((log 4) * (1 + 1 / log 2)) * M := by
  rw [primeTailKernel_eq_harmonicKernel T X (by linarith) hT]
  apply harmonicKernel_bound T (Nat.primesLE ⌊X⌋₊)
    (fun p => 1 / (p : ℝ)) (fun p => log p / log X) hT
    (fun _ _ => by positivity) M _ _ _ hM.le (by positivity) hmass
    (primeHarmonic_large_tail X M hX hM (by linarith) hXM) _
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
  exact primeHarmonic_small_tail X M q hX hM hMquarter hXM hq2 hqM

/-- An explicit `O(M log(2/M)) + o_X(1)` bound with absolute constants. -/
def primeTailConstant : ℝ :=
  log 4 + (2 * log 4 + 2 * log 4 / log 2) * (log 4 * (1 + 1 / log 2)) / log 2

theorem primeTailKernel_bound_log (X M : ℝ) (T : Finset ℕ)
    (hX : 2 ≤ X) (hM : 0 < M) (hMquarter : M < 1 / 4) (hXM : 2 ≤ X ^ M)
    (hT : T ⊆ Nat.primesLE ⌊X⌋₊) (hmass : ∑ p ∈ T, 1 / (p : ℝ) ≤ M) :
    primeTailKernel T X ≤ primeTailConstant * M * log (2 / M) + log 4 / log X := by
  have h := primeTailKernel_bound X M T hX hM hMquarter hXM hT hmass
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogX : 0 < log X := log_pos (by linarith)
  have hD : 0 ≤ log (4 : ℝ) := (log_pos (by norm_num)).le
  let R := (2 * log 4 + 2 * log 4 / log 2) * (log 4 * (1 + 1 / log 2))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hratio : 2 ≤ 2 / M := (le_div_iff₀ hM).2 (by linarith)
  have hloglarge : log 2 ≤ log (2 / M) := log_le_log (by norm_num) hratio
  have hlogsmall : log (1 / M) ≤ log (2 / M) :=
    log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hM.le)
  have hmain := mul_le_mul_of_nonneg_left hlogsmall (mul_nonneg hM.le hD)
  have hratio' : 1 ≤ log (2 / M) / log 2 := (le_div_iff₀ hlog2).2 (by simpa using hloglarge)
  have hrest := mul_le_mul_of_nonneg_left hratio' (mul_nonneg hR hM.le)
  have herr : M * (log 4 / (M * log X)) = log 4 / log X := by field_simp
  change primeTailKernel T X ≤ (log 4 + R / log 2) * M * log (2 / M) + log 4 / log X
  change primeTailKernel T X ≤ M * (log 4 * log (1 / M) + log 4 / (M * log X)) + R * M at h
  rw [mul_add, herr] at h
  simp only [div_eq_mul_inv] at h hmain hrest ⊢
  nlinarith only [h, hmain, hrest]

theorem primeTailKernel_error_tendsto :
    Filter.Tendsto (fun X : ℝ => log 4 / log X) Filter.atTop (nhds 0) :=
  tendsto_log_atTop.const_div_atTop (log 4)

/-- `M` is fixed before the cutoff; all prime sets are quantified after it. -/
theorem primeTailKernel_eventually (M : ℝ) (hM : 0 < M) (hMquarter : M < 1 / 4) :
    ∀ᶠ X : ℝ in Filter.atTop, ∀ T : Finset ℕ,
      T ⊆ Nat.primesLE ⌊X⌋₊ → (∑ p ∈ T, 1 / (p : ℝ)) ≤ M →
      primeTailKernel T X ≤ primeTailConstant * M * log (2 / M) + log 4 / log X := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop hM).eventually (Filter.eventually_ge_atTop (2 : ℝ))] with X hX hXM
  intro T hT hmass
  exact primeTailKernel_bound_log X M T hX hM hMquarter hXM hT hmass

end

end Erdos1122
