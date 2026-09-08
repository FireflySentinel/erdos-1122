import Erdos1122.Normalization
import Erdos1122.ShortIntervalTheorem
import Erdos1122.Clipping

/-! # Arithmetic propositions used by the main implication

Every quantity below is a function from the manuscript. The propositions
state the arithmetic estimates, including their constant and limit quantifiers.
Each is discharged in a separate module and then used in `Main.lean`.
-/

namespace Erdos1122

open Finset Real Filter Topology
open Statements

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

/-- The normalization supplied by Lemma 4.1. -/
structure NormalizedFamily (f : ℕ → ℝ) (M : ℝ) where
  scale : ℝ → ℝ
  slope : ℝ → ℝ
  scale_pos : ∀ X, 0 < scale X
  scale_tendsto : Tendsto scale atTop atTop
  slope_tendsto : Tendsto slope atTop (𝓝 0)
  minimum : ∀ᶠ X in atTop,
    cappedQuadratic (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ))
      (fun p => f p / scale X) (fun p => log p) (slope X) = M ∧
    IsMinOn (cappedQuadratic (Nat.primesLE ⌊X⌋₊) (fun p => 1 / (p : ℝ))
      (fun p => f p / scale X) (fun p => log p)) Set.univ (slope X)

namespace NormalizedFamily

variable {f : ℕ → ℝ} {M : ℝ}

def residual (N : NormalizedFamily f M) (X : ℝ) (p : ℕ) : ℝ :=
  f p / N.scale X - N.slope X * log p

def smallCoefficient (N : NormalizedFamily f M) (X : ℝ) (p : ℕ) : ℝ :=
  if |N.residual X p| ≤ 1 then N.residual X p else 0

def offset (N : NormalizedFamily f M) (X : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊X⌋₊, N.smallCoefficient X p / (p : ℝ)

def comparison (N : NormalizedFamily f M) (K X : ℝ) : ℕ → ℝ :=
  divisorSum (Nat.primesLE ⌊X⌋₊) (fun p => clip K (N.residual X p))

def observable (N : NormalizedFamily f M) (K X : ℝ) (n : ℕ) : ℝ :=
  clip K (f n / N.scale X - N.slope X * log n - N.offset X)

def discrepancy (N : NormalizedFamily f M) (K X : ℝ) : ℝ :=
  initialMean (fun n => (N.observable K X n - (N.comparison K X n - N.offset X)) ^ 2) X

def variance (N : NormalizedFamily f M) (K X : ℝ) : ℝ :=
  initialMean (fun n => (N.comparison K X n - primeCenter (N.comparison K X) X) ^ 2) X

end NormalizedFamily

namespace Statements

/-- The normalization assertion, including convergence of its slope.
Proved in `NormalizedExistence.lean`. -/
def NormalizationExists : Prop :=
  ErdosV → ∀ f : ℕ → ℝ, IsAdditive f → ¬ FiniteConcentration f →
    ∀ M : ℝ, 0 < M → Nonempty (NormalizedFamily f M)

/-- The finite mixed moment (5.5), uniform over the prime coefficients. -/
def Estimate55 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → M < 1 / 4 →
    ∀ᶠ X : ℝ in atTop, ∀ u : ℕ → ℝ,
      (∑ p ∈ Nat.primesLE ⌊X⌋₊, min ((u p) ^ 2) 1 / (p : ℝ)) ≤ M →
      let a := fun p => if |u p| ≤ 1 then u p else 0
      let S := divisorSum (Nat.primesLE ⌊X⌋₊) a
      let μ := ∑ p ∈ Nat.primesLE ⌊X⌋₊, a p / (p : ℝ)
      initialMean (fun n => (S n - μ) ^ 2 *
        if ∃ p ∈ Nat.primesLE ⌊X⌋₊, 1 < |u p| ∧ p ∣ n then 1 else 0) X ≤
          C * M ^ 2 * log (2 / M) + 1 / log X

/-- The comparison of the clipped original function with the centered,
strongly additive one, as in Lemma 5.1. -/
def ClippedComparison : Prop :=
  Estimate55 → ∃ C : ℝ, 0 < C ∧
    ∀ f : ℕ → ℝ, IsAdditive f → ∀ K M : ℝ, 1 < K → 0 < M → M < 1 / 4 →
      ∀ N : NormalizedFamily f M,
        IsBoundedUnder (· ≤ ·) atTop (N.discrepancy K) ∧
        limsup (N.discrepancy K) atTop ≤
          C * (M / K ^ 2 + M ^ 2 * log (2 / M) + K ^ 2 * M ^ 2)

/-- The variance lower bound in Lemma 5.2, with absolute constants fixed
before the function, normalization, and clipping parameters. -/
def ProjectionInstance : Prop :=
  Ruzsa → ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 ≤ C₀ ∧
    ∀ f : ℕ → ℝ, IsAdditive f → ∀ K M : ℝ, 1 < K → 0 < M → M < 1 / 4 →
      ∀ N : NormalizedFamily f M,
        IsBoundedUnder (· ≤ ·) atTop (N.variance K) ∧
        c₀ * M - C₀ * K ^ 2 * M ^ 2 ≤ liminf (N.variance K) atTop

/-- The application of the four-term window comparison in Section 6.
Its short-interval input is exactly the already proved Lemma 2.1. -/
def WindowAssembly : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f →
    Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0) →
    ∀ K M : ℝ, 1 < K → 0 < M → M < 1 / 4 → ∀ N : NormalizedFamily f M,
      IsBoundedUnder (· ≤ ·) atTop (N.discrepancy K) →
      Tendsto (fun H : ℕ => limsup (fun X : ℝ =>
        shortIntervalMoment H (N.comparison K X) X 2) atTop) atTop (𝓝 0) →
      limsup (N.variance K) atTop ≤ 8 * limsup (N.discrepancy K) atTop

end Statements

end

end Erdos1122
