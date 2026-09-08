import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Weighted quadratic projection

The exact finite-dimensional minimization used for the variance lower bound
in Section 5 of the manuscript.
-/

namespace Erdos1122

open Finset

noncomputable section

variable {ι : Type*}

def quadraticMass (t : Finset ι) (w v : ι → ℝ) : ℝ :=
  ∑ i ∈ t, w i * (v i) ^ 2

def weightedPairing (t : Finset ι) (w v l : ι → ℝ) : ℝ :=
  ∑ i ∈ t, w i * v i * l i

theorem quadratic_projection_expansion (t : Finset ι) (w v l : ι → ℝ) (b : ℝ) :
    quadraticMass t w (fun i => v i - b * l i)
      = quadraticMass t w v - 2 * b * weightedPairing t w v l
          + b ^ 2 * quadraticMass t w l := by
  unfold quadraticMass weightedPairing
  simp_rw [show ∀ i, w i * (v i - b * l i) ^ 2 =
    w i * v i ^ 2 - (2 * b) * (w i * v i * l i) + b ^ 2 * (w i * l i ^ 2)
    from fun i => by ring]
  simp [sum_add_distrib, sum_sub_distrib, mul_sum]

theorem quadratic_projection_identity (t : Finset ι) (w v l : ι → ℝ) (b : ℝ)
    (hB : quadraticMass t w l ≠ 0) :
    quadraticMass t w (fun i => v i - b * l i)
      = quadraticMass t w v - (weightedPairing t w v l) ^ 2 / quadraticMass t w l
          + quadraticMass t w l *
              (b - weightedPairing t w v l / quadraticMass t w l) ^ 2 := by
  rw [quadratic_projection_expansion]
  field_simp
  ring

theorem quadratic_projection_lower (t : Finset ι) (w v l : ι → ℝ) (b : ℝ)
    (hB : 0 < quadraticMass t w l) :
    quadraticMass t w v - (weightedPairing t w v l) ^ 2 / quadraticMass t w l
      ≤ quadraticMass t w (fun i => v i - b * l i) := by
  rw [quadratic_projection_identity t w v l b hB.ne']
  exact le_add_of_nonneg_right (mul_nonneg hB.le (sq_nonneg _))

theorem quadratic_projection_attained (t : Finset ι) (w v l : ι → ℝ)
    (hB : quadraticMass t w l ≠ 0) :
    quadraticMass t w
        (fun i => v i - (weightedPairing t w v l / quadraticMass t w l) * l i)
      = quadraticMass t w v - (weightedPairing t w v l) ^ 2 / quadraticMass t w l := by
  rw [quadratic_projection_identity t w v l _ hB]
  simp

/-- An actual global minimizer of the finite quadratic, not merely a lower bound. -/
theorem quadratic_projection_is_minimum (t : Finset ι) (w v l : ι → ℝ)
    (hB : 0 < quadraticMass t w l) (b : ℝ) :
    quadraticMass t w
        (fun i => v i - (weightedPairing t w v l / quadraticMass t w l) * l i)
      ≤ quadraticMass t w (fun i => v i - b * l i) := by
  rw [quadratic_projection_attained t w v l hB.ne']
  exact quadratic_projection_lower t w v l b hB

/-- The explicit form needed when mass and logarithmic correlation are bounded. -/
theorem quadratic_projection_lower_of_bounds (t : Finset ι) (w v l : ι → ℝ)
    (b M R : ℝ) (hB : 0 < quadraticMass t w l)
    (hmass : M ≤ quadraticMass t w v)
    (hpair : |weightedPairing t w v l| ≤ R) :
    M - R ^ 2 / quadraticMass t w l
      ≤ quadraticMass t w (fun i => v i - b * l i) := by
  have hsq : (weightedPairing t w v l) ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_abs (weightedPairing t w v l),
      abs_nonneg (weightedPairing t w v l)]
  have hd := div_le_div_of_nonneg_right hsq hB.le
  have hp := quadratic_projection_lower t w v l b hB
  linarith

end

end Erdos1122
