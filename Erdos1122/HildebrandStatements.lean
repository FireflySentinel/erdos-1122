import Erdos1122.Statements
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # Hildebrand's differences theorem and its corollary

Hildebrand (1988), Theorem 1, pp. 257–258, including formula (1.4), and
its corollary on pp. 258–259. These are propositions, not axioms.
The corollary uses an actual density-one set. The factor in (1.4) is
written with exponent `m + 1` so that the series is indexed by `ℕ`.
-/

namespace Erdos1122.Statements

open Finset Real Filter Topology MeasureTheory ProbabilityTheory

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

/-- Convergence along a set whose complement has natural density zero. -/
def DensityOneZero (g : ℕ → ℝ) : Prop :=
  ∃ S : Set ℕ,
    Tendsto (fun X : ℝ => (#{n ∈ Ioc 0 ⌊X⌋₊ | n ∉ S} : ℝ) / X) atTop (𝓝 0) ∧
    Tendsto g (atTop ⊓ principal S) (𝓝 0)

/-- The real Euler factor in Hildebrand's formula (1.4). -/
def hildebrandFactor (f : ℕ → ℝ) (c : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  1 - 2 / (p : ℝ) + 2 * (1 - 1 / (p : ℝ)) *
    (∑' m : ℕ, Complex.exp (((t * logarithmicResidual f c (p ^ (m + 1)) : ℝ) : ℂ) * Complex.I) /
      (p : ℂ) ^ (m + 1)).re

/-- Weak convergence criterion and characteristic function, with the product
in the natural order of the primes. The measure notation fixes the meaning of
the characteristic function and the right-continuous distribution function. -/
def HildebrandTheorem : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f →
    ((∃ μ : ProbabilityMeasure ℝ,
        IsLimitingDistribution (fun n => f (n + 1) - f n) (cdf (μ : Measure ℝ))) ↔
      ∃ c : ℝ, TruncatedPrimeSummable f c) ∧
    ∀ (μ : ProbabilityMeasure ℝ),
      IsLimitingDistribution (fun n => f (n + 1) - f n) (cdf (μ : Measure ℝ)) →
      ∀ c : ℝ, TruncatedPrimeSummable f c → ∀ t : ℝ,
        Tendsto (fun N : ℕ => ((∏ p ∈ Nat.primesLE N, hildebrandFactor f c p t : ℝ) : ℂ))
          atTop (𝓝 (charFun (μ : Measure ℝ) t))

/-- The corollary as stated: convergence on a density-one set forces a logarithm. -/
def HildebrandCorollary : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → DensityOneZero (fun n => f (n + 1) - f n) →
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → f n = c * log n

/-- Both cited results from the same proved source. -/
def Hildebrand : Prop := HildebrandTheorem ∧ HildebrandCorollary

end

end Erdos1122.Statements
