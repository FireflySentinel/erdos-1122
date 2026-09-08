import Mathlib.NumberTheory.PrimeCounting
import Erdos1122.Variation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The problem and the cited analytic inputs

The cited results are propositions supplied as hypotheses, not axioms.
Arithmetic functions are real-valued; sums and conclusions concern positive integers.

Sources: Mangerel (2022), Theorem 1.1 and Lemma 3.3 (Ruzsa's estimate);
Erdős (1946), Theorem V and its following converse. The intermediate `ErdosX`
statement is proved from Hildebrand's results in `HildebrandBridge.lean`.
-/

namespace Erdos1122.Statements

open Finset Filter Topology Real

noncomputable section

attribute [local instance] Classical.propDecidable

def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b

def decreaseCount (f : ℕ → ℝ) (X : ℝ) : ℕ :=
  #{n ∈ Ioc 0 ⌊X⌋₊ | f (n + 1) < f n}

def ErdosProblem1122 : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f →
    Tendsto (fun X : ℝ => (decreaseCount f X : ℝ) / X) atTop (𝓝 0) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 0 < n → f n = c * log n

def initialMean (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 ⌊X⌋₊, f n) / X

def dyadicMean (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  (2 / X) * ∑ n ∈ Ioc ⌊X / 2⌋₊ ⌊X⌋₊, f n

def primePowerIndices (X : ℝ) : Finset (ℕ × ℕ) :=
  ((Nat.primesLE ⌊X⌋₊).product (Icc 1 ⌊X⌋₊)).filter
    (fun q => ((q.1 ^ q.2 : ℕ) : ℝ) ≤ X)

def primePowerMoment (f : ℕ → ℝ) (X : ℝ) (j : ℕ) : ℝ :=
  ∑ q ∈ primePowerIndices X, |f (q.1 ^ q.2)| ^ j / ((q.1 ^ q.2 : ℕ) : ℝ)

/-- The center in Ruzsa's estimate. -/
def weightedCenter (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ q ∈ primePowerIndices X,
    f (q.1 ^ q.2) / ((q.1 ^ q.2 : ℕ) : ℝ) * (1 - 1 / (q.1 : ℝ))

/-- The prime-power center without the factor `1 - 1/p`. -/
def unweightedCenter (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ q ∈ primePowerIndices X, f (q.1 ^ q.2) / ((q.1 ^ q.2 : ℕ) : ℝ)

/-- The constant precedes the function, the real cutoff and the integer window.
Thus it also applies when the additive function varies with the cutoff. -/
def Mangerel : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℝ, IsAdditive f →
    ∀ X : ℝ, 2 ≤ X → ∀ H : ℕ, 10 ≤ H → (H : ℝ) ≤ X / 100 →
      dyadicMean (fun n => |backwardWindowAverage H f n - dyadicMean f X|) X ≤
        C * (sqrt (log (log H) / log H) + (log X) ^ (-(1 : ℝ) / 800)) *
          sqrt (primePowerMoment f X 2)

def logarithmicResidual (f : ℕ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  f n - c * log n

def ruzsaInfimum (f : ℕ → ℝ) (X : ℝ) : ℝ :=
  sInf (Set.range (fun c : ℝ => c ^ 2 + primePowerMoment (logarithmicResidual f c) X 2))

/-- The two-sided estimate recorded by Mangerel, with an absolute starting
cutoff quantified before the function. The additional comparison with Ruzsa's
explicit coefficient is not needed. -/
def Ruzsa : Prop :=
  ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
    ∀ f : ℕ → ℝ, IsAdditive f → ∀ X : ℝ, X₀ ≤ X →
      c * ruzsaInfimum f X ≤ initialMean (fun n => |f n - weightedCenter f X| ^ 2) X ∧
      initialMean (fun n => |f n - weightedCenter f X| ^ 2) X ≤ C * ruzsaInfimum f X

def FiniteConcentration (f : ℕ → ℝ) : Prop :=
  ∃ d R : ℝ, 0 < d ∧ 0 < R ∧ ∀ Y : ℝ, ∃ X : ℝ, Y ≤ X ∧ 1 ≤ X ∧
    ∃ a : ℝ, d * X ≤ (#{n ∈ Ioc 0 ⌊X⌋₊ | a ≤ f n ∧ f n ≤ a + R} : ℝ)

def TruncatedPrimeSummable (f : ℕ → ℝ) (c : ℝ) : Prop :=
  Summable (fun p : {p : ℕ // p.Prime} =>
    min ((f p.val - c * log p.val) ^ 2) 1 / (p.val : ℝ))

/-- Theorem V together with the converse in the paragraph immediately after it. -/
def ErdosV : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f →
    (FiniteConcentration f ↔ ∃ c : ℝ, TruncatedPrimeSummable f c)

/-- Standard right-continuous distribution convention: empirical distribution
functions converge at continuity points. This does not prescribe values of
empirical limits at atoms. -/
def IsLimitingDistribution (g : ℕ → ℝ) (D : ℝ → ℝ) : Prop :=
  Monotone D ∧ (∀ x, ContinuousWithinAt D (Set.Ici x) x) ∧
    Tendsto D atBot (𝓝 0) ∧ Tendsto D atTop (𝓝 1) ∧
    ∀ x : ℝ, ContinuousAt D x →
      Tendsto (fun X : ℝ => (#{n ∈ Ioc 0 ⌊X⌋₊ | g n ≤ x} : ℝ) / X)
        atTop (𝓝 (D x))

/-- Precisely the parts of Theorem X used by the manuscript. The conclusion
concerns every positive integer, including all higher prime powers. -/
def ErdosX : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → ∀ c : ℝ, TruncatedPrimeSummable f c →
    ∃ D : ℝ → ℝ, IsLimitingDistribution (fun n => f (n + 1) - f n) D ∧
      ((∀ x : ℝ, x < 0 → D x = 0) ↔ ∀ n : ℕ, 0 < n → f n = c * log n)

end

end Erdos1122.Statements
