import Erdos1122.PrimeProjection
import Erdos1122.MovingCenters
import Erdos1122.SecondMoment

/-! # Lemma 5.2 from the stated Ruzsa theorem -/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

/-- Retaining only exponent one gives a lower bound for the full
prime-power second moment. -/
theorem primeMoment_le_primePowerMoment (f : ℕ → ℝ) (X : ℝ) (hX : 2 ≤ X) :
    primeMoment f X 2 ≤ primePowerMoment f X 2 := by
  classical
  let P := Nat.primesLE ⌊X⌋₊
  have hin : P.image (fun p => (p, 1)) ⊆ primePowerIndices X := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
    refine mem_filter.2 ⟨mem_product.2 ⟨hp, mem_Icc.2 ⟨le_rfl, ?_⟩⟩, ?_⟩
    · exact (Nat.one_le_floor_iff X).2 (by linarith)
    · simpa only [pow_one] using (Nat.le_floor_iff (by linarith)).1 (Nat.mem_primesLE.1 hp).1
  have hh := sum_le_sum_of_subset_of_nonneg hin
    (f := fun q : ℕ × ℕ => |f (q.1 ^ q.2)| ^ 2 / ((q.1 ^ q.2 : ℕ) : ℝ))
    (fun _ _ _ => by positivity)
  rw [sum_image (fun _ _ _ _ h => congrArg Prod.fst h)] at hh
  simpa only [pow_one, P, primeMoment, primePowerMoment] using hh

/-- The lower-variance proposition used by `main_of_cited` is proved,
including the actual Ruzsa infimum and its change of center. -/
theorem projection_instance : ProjectionInstance := by
  intro hR
  obtain ⟨Ctk, hCtk, hTK⟩ := stronglyAdditive_second_moment hR
  obtain ⟨c₀, C, X₀, hc₀, _hC, hX₀, hR⟩ := hR
  refine ⟨c₀ / 2, (c₀ / 2) * (8 / log 2), by positivity, by positivity, ?_⟩
  intro f _hf K M hK hM _hMq N
  have hK0 : 0 ≤ K := by linarith
  have hbound : IsBoundedUnder (· ≤ ·) atTop (N.variance K) := by
    refine ⟨Ctk * (K ^ 2 * M), ?_⟩
    change ∀ᶠ X in atTop, N.variance K X ≤ Ctk * (K ^ 2 * M)
    filter_upwards [N.comparison_mass K hK.le, eventually_ge_atTop (3 : ℝ)] with X hm hX
    exact (hTK _ (N.comparison_stronglyAdditive K X) X hX).trans
      (mul_le_mul_of_nonneg_left hm hCtk.le)
  refine ⟨hbound, ?_⟩
  let L := fun X : ℝ => M - (N.slope X) ^ 2 -
    (8 / log 2) * (|N.slope X| / log X + K * M) ^ 2
  let e := fun X : ℝ => weightedCenter (N.comparison K X) X - primeCenter (N.comparison K X) X
  let A := fun X : ℝ => (c₀ / 2) * L X - (e X) ^ 2
  have hA : Tendsto A atTop (𝓝 ((c₀ / 2) * M - ((c₀ / 2) * (8 / log 2)) * K ^ 2 * M ^ 2)) := by
    convert! ((N.comparison_prime_projection_lower_tendsto K).const_mul (c₀ / 2)).sub
      ((N.comparison_center_tendsto K hK0).pow 2) using 1
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    ring_nf
  have hpoint : ∀ᶠ X in atTop, A X ≤ N.variance K X := by
    filter_upwards [N.comparison_prime_projection K hK.le, eventually_ge_atTop X₀] with X hp hX
    have hinf : L X ≤ ruzsaInfimum (N.comparison K X) X := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨b, rfl⟩
      have hpr := primeMoment_le_primePowerMoment (logarithmicResidual (N.comparison K X) b) X (by linarith)
      have heq : primeMoment (logarithmicResidual (N.comparison K X) b) X 2 =
          ∑ p ∈ Nat.primesLE ⌊X⌋₊, (clip K (N.residual X p) - b * log p) ^ 2 / (p : ℝ) := by
        unfold primeMoment
        apply sum_congr rfl
        intro p hpp
        dsimp [logarithmicResidual]
        rw [N.comparison_prime K X p (Nat.prime_of_mem_primesLE hpp), if_pos hpp, sq_abs]
      rw [heq] at hpr
      have hh := (hp b).trans hpr
      linarith [sq_nonneg b]
    have hlow := (mul_le_mul_of_nonneg_left hinf hc₀.le).trans
      (hR _ (N.comparison_stronglyAdditive K X).isAdditive X hX).1
    simp only [sq_abs] at hlow
    have hs := second_moment_center_shift (N.comparison K X)
      (weightedCenter (N.comparison K X) X) (primeCenter (N.comparison K X) X) X (by linarith)
    change A X ≤ initialMean (fun n => (N.comparison K X n - primeCenter (N.comparison K X) X) ^ 2) X
    dsimp only [A, e]
    nlinarith only [hlow, hs]
  have hh := liminf_le_liminf hpoint hA.isBoundedUnder_ge hbound.isCoboundedUnder_ge
  rwa [hA.liminf_eq] at hh

end

end Erdos1122
