import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The finite harmonic kernel in Lemma 3.1

Write `x p = log p / log X` and `w p = 1/p`. Split the inner prime
sum at `x q = M`. The large `q` terms use only the mass of `T`;
for small `q`, interchange the sums and use the local tail bound.
-/

namespace Erdos1122

open Finset

noncomputable section

variable {ι : Type*}

def harmonicKernel (T P : Finset ι) (w x : ι → ℝ) : ℝ :=
  ∑ p ∈ T, w p * ∑ q ∈ P, if 1 < x p + x q then w q else 0

theorem harmonicKernel_swap (T P : Finset ι) (w x : ι → ℝ) :
    harmonicKernel T P w x =
      ∑ q ∈ P, w q * ∑ p ∈ T, if 1 < x p + x q then w p else 0 := by
  unfold harmonicKernel
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- The finite estimate, before inserting any prime-sum theorem.
`hhigh`, `hlocal`, and `hmoment` are precisely the three analytic inputs. -/
theorem harmonicKernel_bound (T P : Finset ι) (w x : ι → ℝ)
    (hTP : T ⊆ P) (hw : ∀ p ∈ P, 0 ≤ w p)
    (M L C D : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hmass : ∑ p ∈ T, w p ≤ M)
    (hhigh : (∑ q ∈ P, if M < x q then w q else 0) ≤ L)
    (hlocal : ∀ q ∈ P, x q ≤ M →
      (∑ p ∈ P, if 1 < x p + x q then w p else 0) ≤ C * x q)
    (hmoment : (∑ q ∈ P, if x q ≤ M then w q * x q else 0) ≤ D * M) :
    harmonicKernel T P w x ≤ M * L + C * D * M := by
  rw [harmonicKernel_swap]
  have hpoint (q : ι) (hq : q ∈ P) :
      w q * (∑ p ∈ T, if 1 < x p + x q then w p else 0) ≤
        M * (if M < x q then w q else 0) +
          C * (if x q ≤ M then w q * x q else 0) := by
    by_cases hqM : M < x q
    · simp only [if_pos hqM, if_neg (not_le_of_gt hqM), mul_zero, add_zero]
      rw [mul_comm M]
      apply mul_le_mul_of_nonneg_left _ (hw q hq)
      apply le_trans _ hmass
      exact sum_le_sum fun p hp => by split_ifs <;> first | rfl | exact hw p (hTP hp)
    · have hqM' : x q ≤ M := le_of_not_gt hqM
      simp only [if_neg hqM, if_pos hqM', mul_zero, zero_add]
      have hsub : (∑ p ∈ T, if 1 < x p + x q then w p else 0) ≤
          ∑ p ∈ P, if 1 < x p + x q then w p else 0 := by
        apply sum_le_sum_of_subset_of_nonneg hTP
        intro p hp _
        split_ifs <;> first | exact hw p hp | exact le_rfl
      have h := mul_le_mul_of_nonneg_left (hsub.trans (hlocal q hq hqM')) (hw q hq)
      nlinarith
  calc
    _ ≤ ∑ q ∈ P, (M * (if M < x q then w q else 0) +
        C * (if x q ≤ M then w q * x q else 0)) := sum_le_sum hpoint
    _ = M * (∑ q ∈ P, if M < x q then w q else 0) +
        C * (∑ q ∈ P, if x q ≤ M then w q * x q else 0) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left hhigh hM
      have h₂ := mul_le_mul_of_nonneg_left hmoment hC
      nlinarith

/-- Subtracting two Mertens estimates in logarithmic coordinates.
For prime harmonic sums, `H t` denotes the sum over primes at most `exp t`.
The additive constant cancels; both error terms remain explicit. -/
theorem mertens_difference_bound (H : ℝ → ℝ) (B A s t : ℝ)
    (hs : 0 < s) (ht : 0 < t)
    (h₁ : |H t - Real.log t - B| ≤ A / t)
    (h₂ : |H s - Real.log s - B| ≤ A / s) :
    H t - H s ≤ Real.log (t / s) + A / t + A / s := by
  rw [Real.log_div ht.ne' hs.ne']
  have h₁' := (abs_le.mp h₁).2
  have h₂' := (abs_le.mp h₂).1
  linarith

/-- The local logarithmic bound used when `q ≤ X^M` and `M < 1/4`. -/
theorem log_reciprocal_one_sub_le (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    Real.log (1 / (1 - x)) ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hp)
  have hr : 1 / (1 - x) - 1 ≤ 2 * x := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ hp).2
    nlinarith
  exact h.trans hr

end

end Erdos1122
