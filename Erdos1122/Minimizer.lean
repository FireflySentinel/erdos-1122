import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# The finite capped quadratic in Lemma 4.1

A smooth quadratic branch lying above the capped objective and touching it
at a local minimum also has a local minimum there. At a breakpoint, choosing
the quadratic or constant branch gives incompatible stationary equations.
This avoids taking a derivative of the capped function at a breakpoint.
-/

namespace Erdos1122

open Finset Filter Topology

noncomputable section

variable {ι : Type*}

def cappedQuadratic (t : Finset ι) (w a l : ι → ℝ) (c : ℝ) : ℝ :=
  c ^ 2 + ∑ i ∈ t, w i * min ((a i - c * l i) ^ 2) 1

theorem cappedQuadratic_continuous (t : Finset ι) (w a l : ι → ℝ) :
    Continuous (cappedQuadratic t w a l) := by
  unfold cappedQuadratic
  fun_prop

theorem sq_le_cappedQuadratic (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (c : ℝ) :
    c ^ 2 ≤ cappedQuadratic t w a l c := by
  exact le_add_of_nonneg_right (sum_nonneg fun i hi =>
    mul_nonneg (hw i hi) (le_min (sq_nonneg _) zero_le_one))

theorem cappedQuadratic_coercive (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) :
    Tendsto (cappedQuadratic t w a l) (cocompact ℝ) atTop := by
  have hs : Tendsto (fun c : ℝ => c ^ 2) (cocompact ℝ) atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs, sq_abs] using
      (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp
        (tendsto_norm_cocompact_atTop (E := ℝ))
  exact tendsto_atTop_mono (sq_le_cappedQuadratic t w a l hw) hs

theorem cappedQuadratic_exists_min (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) :
    ∃ c : ℝ, ∀ x : ℝ, cappedQuadratic t w a l c ≤ cappedQuadratic t w a l x :=
  (cappedQuadratic_continuous t w a l).exists_forall_le
    (cappedQuadratic_coercive t w a l hw)

private def quadraticBranch (t : Finset ι) (w a l : ι → ℝ)
    (s : ι → Prop) (c : ℝ) : ℝ := by
  classical
  exact c ^ 2 + ∑ i ∈ t, if s i then w i * (a i - c * l i) ^ 2 else w i

private theorem branch_derivative (t : Finset ι) (w a l : ι → ℝ)
    (s : ι → Prop) [DecidablePred s] (c : ℝ) :
    HasDerivAt (quadraticBranch t w a l s)
      (2 * c - 2 * ∑ i ∈ t, if s i then w i * (a i - c * l i) * l i else 0) c := by
  classical
  have hi (i : ι) : HasDerivAt
      (fun x : ℝ => if s i then w i * (a i - x * l i) ^ 2 else w i)
      (if s i then -2 * (w i * (a i - c * l i) * l i) else 0) c := by
    by_cases h : s i
    · simp only [if_pos h]
      convert! ((((hasDerivAt_id c).mul_const (l i)).const_sub (a i)).pow 2).const_mul
        (w i) using 1
      simp
      ring
    · simpa only [if_neg h] using hasDerivAt_const c (w i)
  convert! ((hasDerivAt_id c).pow 2).add (HasDerivAt.fun_sum (u := t) fun i _ => hi i) using 1
  · ext x
    simp only [quadraticBranch, Pi.add_apply, Pi.pow_apply, id_eq]
    congr 1
    apply sum_congr rfl
    intro i _
    split_ifs <;> rfl
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
    simp_rw [show ∀ i, (if s i then -2 * (w i * (a i - c * l i) * l i) else 0) =
      -2 * (if s i then w i * (a i - c * l i) * l i else 0) from
      fun i => by split_ifs <;> ring]
    rw [← mul_sum]
    ring

private theorem branch_stationary (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (s : ι → Prop) [DecidablePred s] (c : ℝ)
    (hmin : IsLocalMin (cappedQuadratic t w a l) c)
    (hs : ∀ i ∈ t, (s i → (a i - c * l i) ^ 2 ≤ 1) ∧
      (¬s i → 1 ≤ (a i - c * l i) ^ 2)) :
    (∑ i ∈ t, if s i then w i * (a i - c * l i) * l i else 0) = c := by
  classical
  have hle (x : ℝ) : cappedQuadratic t w a l x ≤ quadraticBranch t w a l s x := by
    unfold cappedQuadratic quadraticBranch
    apply add_le_add_right
    apply sum_le_sum
    intro i hi
    split_ifs
    · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hw i hi)
    · simpa using mul_le_mul_of_nonneg_left (min_le_right ((a i - x * l i) ^ 2) 1)
        (hw i hi)
  have heq : cappedQuadratic t w a l c = quadraticBranch t w a l s c := by
    unfold cappedQuadratic quadraticBranch
    congr 1
    apply sum_congr rfl
    intro i hi
    by_cases h : s i
    · simp [h, min_eq_left ((hs i hi).1 h)]
    · simp [h, min_eq_right ((hs i hi).2 h)]
  have hm : IsLocalMin (quadraticBranch t w a l s) c := by
    filter_upwards [hmin] with x hx
    exact heq ▸ hx.trans (hle x)
  have hz := hm.hasDerivAt_eq_zero (branch_derivative t w a l s c)
  linarith

theorem cappedQuadratic_stationary (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (c : ℝ)
    (hmin : IsLocalMin (cappedQuadratic t w a l) c) :
    (∑ i ∈ t, if (a i - c * l i) ^ 2 < 1
      then w i * (a i - c * l i) * l i else 0) = c := by
  apply branch_stationary t w a l hw (fun i => (a i - c * l i) ^ 2 < 1) c hmin
  intro i _
  exact ⟨le_of_lt, le_of_not_gt⟩

/-- Every local minimum avoids each breakpoint with positive weight and nonzero slope. -/
theorem cappedQuadratic_no_breakpoint (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (c : ℝ)
    (hmin : IsLocalMin (cappedQuadratic t w a l) c)
    (i : ι) (hi : i ∈ t) (hwi : 0 < w i) (hli : l i ≠ 0) :
    |a i - c * l i| ≠ 1 := by
  classical
  intro habs
  have heq : (a i - c * l i) ^ 2 = 1 := by nlinarith [sq_abs (a i - c * l i)]
  have hbase := cappedQuadratic_stationary t w a l hw c hmin
  have hextra := branch_stationary t w a l hw
    (fun j => j = i ∨ (a j - c * l j) ^ 2 < 1) c hmin (by
      intro j _
      constructor
      · rintro (rfl | h)
        · exact heq.le
        · exact h.le
      · intro h
        exact le_of_not_gt (fun hlt => h (Or.inr hlt)))
  have hsum : (∑ j ∈ t, if j = i ∨ (a j - c * l j) ^ 2 < 1
        then w j * (a j - c * l j) * l j else 0) =
      w i * (a i - c * l i) * l i +
        ∑ j ∈ t, if (a j - c * l j) ^ 2 < 1
          then w j * (a j - c * l j) * l j else 0 := by
    calc
      _ = ∑ j ∈ t, ((if j = i then w i * (a i - c * l i) * l i else 0) +
          (if (a j - c * l j) ^ 2 < 1 then w j * (a j - c * l j) * l j else 0)) := by
        apply sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp [heq]
        · simp [hji]
      _ = _ := by simp [sum_add_distrib, hi]
  have hz : w i * (a i - c * l i) * l i = 0 := by linarith
  have hu : a i - c * l i ≠ 0 := by intro h; simp [h] at heq
  exact mul_ne_zero (mul_ne_zero hwi.ne' hu) hli hz

/-- Equation (4.3), with the manuscript's absolute-value cutoff. -/
theorem cappedQuadratic_stationary_abs (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (c : ℝ)
    (hmin : IsLocalMin (cappedQuadratic t w a l) c) :
    (∑ i ∈ t, if |a i - c * l i| < 1
      then w i * (a i - c * l i) * l i else 0) = c := by
  simpa only [sq_lt_one_iff_abs_lt_one] using cappedQuadratic_stationary t w a l hw c hmin

/-- The complete finite-dimensional conclusion needed in Lemma 4.1. -/
theorem cappedQuadratic_minimizer (t : Finset ι) (w a l : ι → ℝ)
    (hw : ∀ i ∈ t, 0 < w i) (hl : ∀ i ∈ t, l i ≠ 0) :
    ∃ c : ℝ, (∀ x : ℝ, cappedQuadratic t w a l c ≤ cappedQuadratic t w a l x) ∧
      (∀ i ∈ t, |a i - c * l i| ≠ 1) ∧
      (∑ i ∈ t, if |a i - c * l i| < 1
        then w i * (a i - c * l i) * l i else 0) = c := by
  have hw0 : ∀ i ∈ t, 0 ≤ w i := fun i hi => (hw i hi).le
  obtain ⟨c, hc⟩ := cappedQuadratic_exists_min t w a l hw0
  have hlocal : IsLocalMin (cappedQuadratic t w a l) c := Filter.Eventually.of_forall hc
  exact ⟨c, hc, fun i hi => cappedQuadratic_no_breakpoint t w a l hw0 c hlocal
    i hi (hw i hi) (hl i hi), cappedQuadratic_stationary_abs t w a l hw0 c hlocal⟩

end

end Erdos1122
