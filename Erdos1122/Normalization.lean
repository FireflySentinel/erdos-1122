import Erdos1122.Statements
import Erdos1122.Scale

/-! # Fixed-scale divergence from Erdős's concentration theorem

Nested compact sublevel sets express the compactness step directly. A point
in their intersection bounds every finite partial sum of the nonnegative
prime series, which proves summability.
-/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

noncomputable section

def normalizationValue (f : ℕ → ℝ) (X s : ℝ) : ℝ :=
  scaledMinimum (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ)) f (fun p => log p) s

private theorem primeQuadratic_mono (f : ℕ → ℝ) (s c X Y : ℝ) (hXY : X ≤ Y) :
    cappedQuadratic (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ)) (fun p => f p / s) (fun p => log p) c ≤
      cappedQuadratic (Nat.primesLE ⌊Y⌋₊) (fun p => 1 / (p : ℝ)) (fun p => f p / s) (fun p => log p) c := by
  unfold cappedQuadratic
  apply add_le_add le_rfl
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.2 ⟨(Nat.mem_primesLE.1 hp).1.trans (Nat.floor_le_floor hXY),
      (Nat.mem_primesLE.1 hp).2⟩
  · intro p _ _
    exact mul_nonneg (by positivity) (le_min (sq_nonneg _) zero_le_one)

theorem normalizationValue_monotone (f : ℕ → ℝ) (s : ℝ) :
    Monotone (fun X => normalizationValue f X s) := by
  intro X Y hXY
  obtain ⟨c, hc, _⟩ := scaledMinimum_attained (Nat.primesLE ⌊Y⌋₊)
    (fun p => 1 / (p : ℝ)) f (fun p => log p) (fun _ _ => by positivity) s
  change normalizationValue f X s ≤ scaledMinimum _ _ _ _ s
  rw [hc]
  exact (scaledMinimum_le _ _ _ _ (fun _ _ => by positivity) s c).trans
    (primeQuadratic_mono f s c X Y hXY)

private theorem bounded_normalization_summable (f : ℕ → ℝ) (s B : ℝ)
    (hb : ∀ N : ℕ, normalizationValue f N s ≤ B) :
    ∃ c : ℝ, Summable (fun p : {p : ℕ // p.Prime} =>
      min ((f p.val / s - c * log p.val) ^ 2) 1 / (p.val : ℝ)) := by
  let G : ℕ → ℝ → ℝ := fun N => cappedQuadratic (Nat.primesLE N)
    (fun p => 1 / (p : ℝ)) (fun p => f p / s) (fun p => log p)
  let T : ℕ → Set ℝ := fun N => {c | G N c ≤ B}
  have hc (N : ℕ) : IsClosed (T N) :=
    isClosed_le (cappedQuadratic_continuous _ _ _ _) continuous_const
  have hn (N : ℕ) : (T N).Nonempty := by
    obtain ⟨c, he, _⟩ := scaledMinimum_attained (Nat.primesLE N)
      (fun p => 1 / (p : ℝ)) f (fun p => log p) (fun _ _ => by positivity) s
    refine ⟨c, ?_⟩
    have h := hb N
    simpa only [normalizationValue, Nat.floor_natCast, he, T, Set.mem_ofPred_eq, G] using h
  have hB : 0 ≤ B := by
    obtain ⟨c, hc⟩ := hn 0
    have hs := sq_le_cappedQuadratic (Nat.primesLE 0) (fun p => 1 / (p : ℝ))
      (fun p => f p / s) (fun p => log p) (fun _ _ => by positivity) c
    exact (sq_nonneg c).trans (hs.trans hc)
  have hcompact : IsCompact (T 0) := by
    apply isCompact_Icc.of_isClosed_subset (hc 0)
    intro c hc
    have hs := sq_le_cappedQuadratic (Nat.primesLE 0) (fun p => 1 / (p : ℝ))
      (fun p => f p / s) (fun p => log p) (fun _ _ => by positivity) c
    have hsq : c ^ 2 ≤ B := hs.trans hc
    show c ∈ Set.Icc (-(B + 1)) (B + 1)
    constructor <;> nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  have hnest (N : ℕ) : T (N + 1) ⊆ T N := by
    intro c hc
    have hm := primeQuadratic_mono f s c (N : ℝ) ((N + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.le_succ N)
    simp only [Nat.floor_natCast] at hm
    exact hm.trans hc
  obtain ⟨c, hcAll⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hnest hn hcompact hc
  refine ⟨c, summable_of_sum_le (c := B) (fun p => ?_) (fun U => ?_)⟩
  · exact div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity)
  · let N := U.sup (fun p => p.val)
    have hcN : G N c ≤ B := Set.mem_iInter.1 hcAll N
    have hsum : (∑ p ∈ U, min ((f p.val / s - c * log p.val) ^ 2) 1 / (p.val : ℝ)) ≤
        ∑ p ∈ Nat.primesLE N, min ((f p / s - c * log p) ^ 2) 1 / (p : ℝ) := by
      classical
      calc
        _ = ∑ p ∈ U.image (fun p => p.val), min ((f p / s - c * log p) ^ 2) 1 / (p : ℝ) := by
          rw [sum_image (fun _ _ _ _ h => Subtype.ext h)]
        _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
            exact Nat.mem_primesLE.2 ⟨le_sup hq, q.property⟩
          · intro _ _ _
            exact div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity)
    apply hsum.trans
    have hsq := sq_nonneg c
    dsimp [G, cappedQuadratic] at hcN
    simp only [div_eq_mul_inv, mul_comm, mul_one] at hcN ⊢
    linarith

private theorem truncated_rescale_summable (f : ℕ → ℝ) (s c : ℝ) (hs : 0 < s)
    (h : Summable (fun p : {p : ℕ // p.Prime} =>
      min ((f p.val / s - c * log p.val) ^ 2) 1 / (p.val : ℝ))) :
    TruncatedPrimeSummable f (s * c) := by
  have hC : 0 ≤ max (s ^ 2) 1 := (sq_nonneg s).trans (le_max_left _ _)
  apply (h.mul_left (max (s ^ 2) 1)).of_nonneg_of_le
  · intro p
    exact div_nonneg (le_min (sq_nonneg _) zero_le_one) (by positivity)
  · intro p
    have he : f p.val - s * c * log p.val = s * (f p.val / s - c * log p.val) := by field_simp
    change min ((f p.val - s * c * log p.val) ^ 2) 1 / (p.val : ℝ) ≤ _
    rw [he, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    by_cases hu : (f p.val / s - c * log p.val) ^ 2 ≤ 1
    · rw [min_eq_left hu]
      exact (min_le_left _ _).trans (by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    · rw [min_eq_right (le_of_not_ge hu), mul_one]
      exact (min_le_right _ _).trans (le_max_right _ _)

/-- Lemma 4.1's fixed-scale divergence, conditional only on Erdős V. -/
theorem normalizationValue_tendsto_atTop (hV : ErdosV) (f : ℕ → ℝ)
    (hf : IsAdditive f) (hnoconc : ¬ FiniteConcentration f) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun X : ℝ => normalizationValue f X s) atTop atTop := by
  apply (normalizationValue_monotone f s).tendsto_atTop_atTop_iff.2
  intro B
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := bounded_normalization_summable f s B (fun N => (h N).le)
  exact hnoconc ((hV f hf).2 ⟨s * c, truncated_rescale_summable f s c hs hc⟩)


/-- The prescribed positive mass is attained for every sufficiently large cutoff. -/
theorem normalization_level_eventually (hV : ErdosV) (f : ℕ → ℝ)
    (hf : IsAdditive f) (hnoconc : ¬ FiniteConcentration f) (M : ℝ) (hM : 0 < M) :
    ∀ᶠ X : ℝ in atTop, ∃ s : ℝ, 1 < s ∧ normalizationValue f X s = M := by
  filter_upwards [(normalizationValue_tendsto_atTop hV f hf hnoconc 1 (by norm_num)).eventually
    (eventually_gt_atTop M)] with X hX
  exact scaledMinimum_exists_scale (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ)) f
    (fun p => log p) (fun _ _ => by positivity) 1 M (by norm_num) hM hX

/-- Applying the scale theorem to the actual normalization removes its
fixed-scale divergence hypothesis. -/
theorem normalization_scales_tendsto_atTop (hV : ErdosV) (f : ℕ → ℝ)
    (hf : IsAdditive f) (hnoconc : ¬ FiniteConcentration f) (s : ℝ → ℝ) (M : ℝ)
    (hlevel : ∀ᶠ X in atTop, 0 < s X ∧ normalizationValue f X (s X) = M) :
    Tendsto s atTop atTop := by
  apply scales_tendsto_atTop_of_level (normalizationValue f) s M
    (fun X => scaledMinimum_antitoneOn (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ)) f
      (fun p => log p) (fun _ _ => by positivity))
    (fun r hr => normalizationValue_tendsto_atTop hV f hf hnoconc r hr) hlevel

end

end Erdos1122
