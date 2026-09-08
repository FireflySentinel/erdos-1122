# Lean formalization

[`Main.lean`](Erdos1122/Main.lean) proves the complete implication

```lean
Erdos1122.Statements.main_of_cited :
  Mangerel → Ruzsa → Elliott → ErdosV → Hildebrand → ErdosProblem1122
```

There are **no intermediate arithmetic hypotheses** in this theorem. Its
conclusion is the original statement: every real additive function whose
set of decreases has density zero equals `c * log n` on every positive
integer, for some `c ≥ 0`.

The cited results are propositions supplied as theorem hypotheses.
`Hildebrand` is the conjunction of his differences theorem and its corollary.
Their proofs are not formalized in this repository. Thus Lean checks the
implication from those precise statements, not an unconditional proof of
all the cited mathematics. Checking the statements against the literature
remains part of reviewing the manuscript.

## Cited inputs and their sources

[`Statements.lean`](Erdos1122/Statements.lean) defines positive-integer
coprime additivity, `decreaseCount`, the problem, and the moment and
concentration inputs. [`HildebrandStatements.lean`](Erdos1122/HildebrandStatements.lean)
defines the two Hildebrand propositions.
The constants in the moment and short-interval estimates are quantified
before the function and the cutoff. In `Mangerel`, the window is an integer
with `10 ≤ H` and `(H : ℝ) ≤ X / 100`. The cutoff `X` is real throughout.

| Proposition | Source and convention |
|---|---|
| `Mangerel` | [Mangerel, Theorem 1.1](https://doi.org/10.1007/s11139-022-00623-y), specialized to real additive functions. The backward window and dyadic mean are actual finite sums. |
| `Ruzsa` | The two-sided second-moment estimate in Mangerel, published Lemma 3.3 (arXiv v1, Lemma 2.3), attributed to [Ruzsa, 1983](https://doi.org/10.1007/978-3-0348-5438-2_50). Its center has the factor `1 - 1/p`. |
| `Elliott` | [Elliott, 1980, Theorem 1](https://doi.org/10.4153/CJM-1980-068-0), at exponent four. The original article's definition of `A(x)` on p. 893 is the unweighted prime-power center. |
| `ErdosV` | [Erdős, 1946](https://combinatorica.hu/~p_erdos/1946-06.pdf), Theorem V and the converse in the following paragraph: finite concentration is equivalent to a summable truncated prime residual for some logarithmic coefficient. |
| `HildebrandTheorem` | [Hildebrand, 1988, Theorem 1](https://doi.org/10.1090/S0002-9947-1988-0965752-X), pp. 257–258: the weak-convergence criterion and the characteristic-function formula (1.4). |
| `HildebrandCorollary` | The corollary on pp. 258–259 of the same paper: convergence of the increments to zero on a density-one set forces a logarithm. Its proof is printed there. |

The two prime-power centers are kept distinct:

\[
 A_w(f,X)=\sum_{p^k\le X}\frac{f(p^k)}{p^k}(1-1/p),
 \qquad
 A_u(f,X)=\sum_{p^k\le X}\frac{f(p^k)}{p^k}.
\]

[`CenterShift.lean`](Erdos1122/CenterShift.lean) proves, without an
additivity assumption,

\[
 |A_w-A_u|\le
 \left(\sum_{p^k\le X}p^{-k-2}\right)^{1/2}
 \left(\sum_{p^k\le X}|f(p^k)|^2/p^k\right)^{1/2}.
\]

It also proves `elliott_iff_weighted`, so either center convention for
Elliott implies the other with an absolute change of constant.
[`SecondMoment.lean`](Erdos1122/SecondMoment.lean) derives the
Turán–Kubilius upper bound at both centers from `Ruzsa`, using the
competitor `c = 0`. It then proves the strongly additive bound at the
prime center, including the finite cases `1 ≤ X < 2` and `2 ≤ X < 3`.
This is an upper-bound transfer; it is not presented as an equivalence of
the entire two-sided Ruzsa statements at arbitrary centers.

**Cutoff ranges.** Elliott's original Theorem 1 explicitly states uniformity
for real `X ≥ 2`. Mangerel's published Theorem 1.1 states the integer range
`10 ≤ H ≤ X/100`, which already requires `X ≥ 1000`; no additional
starting threshold is stated there. Ruzsa's proposition quantifies
absolute constants `c, C, X₀`, with
`X₀ ≥ 3`, before the function, and assumes the two-sided estimate only
for `X ≥ X₀`. The lower bound is used only eventually.

[`FiniteCutoffMoment.lean`](Erdos1122/FiniteCutoffMoment.lean) supplies
all smaller scales for the upper bound. For `0 < X ≤ B`, the additive
prime-power expansion and finite Cauchy–Schwarz give

\[
 \mathbb E_X|f-A_w(f,X)|^2
 \le 2\bigl(B\lfloor B\rfloor+\#\{(p,k):p\text{ prime},\ k\ge1,\ p^k\le B\}\bigr)
       \sum_{p^k\le X}|f(p^k)|^2/p^k.
\]

The constant depends on `B` alone. Taking `B = X₀` therefore extends the
upper estimate without a new cited input or a finite-range lower estimate.

## The Hildebrand bridge

[`HildebrandBridge.lean`](Erdos1122/HildebrandBridge.lean) proves
`hildebrand_implies_erdosX : Hildebrand → ErdosX`. Thus `ErdosX` remains
a useful intermediate statement, but it is no longer a hypothesis of the
main theorem. Erdős announced Theorems IX and X without proof on p. 17
of his 1946 paper, and subsequently used X in XI; the present argument
uses Hildebrand's proved theorem and corollary instead.

The theorem proposition includes both directions of the weak-convergence
criterion and the formula, for `h(n) = f(n) - c log n`,

\[
 \widehat\mu(t)=\prod_p\left(1-\frac2p+
  2(1-1/p)\operatorname{Re}\sum_{k\ge1}
       \frac{e^{it h(p^k)}}{p^k}\right).
\]

The product is a limit over primes in their natural order. The definition
uses a probability measure and its actual characteristic function; it does
not assume symmetry. Weak convergence is expressed at continuity points
of the right-continuous cumulative distribution function. The original
normalization by `floor X` and the repository's normalization by `X`
have the same limit because `floor X / X → 1`.

[`SymmetricDistribution.lean`](Erdos1122/SymmetricDistribution.lean)
proves that the real characteristic-function limit makes the measure
invariant under `x ↦ -x`, by uniqueness of characteristic functions.
A symmetric probability measure with no negative mass is `dirac 0`.
The same file proves that this limiting law makes every fixed-tolerance
exceptional set have density zero.
[`DensityOne.lean`](Erdos1122/DensityOne.lean) extracts one density-one
set on which the ordinary limit is zero. It chooses a cutoff for each
tolerance and uses the nesting of exceptional sets to control their union
by the last active tolerance. This supplies the literal hypothesis of
`HildebrandCorollary`; density-one extraction is not an extra assumption.
Finally, [`LogarithmicRigidity.lean`](Erdos1122/LogarithmicRigidity.lean)
identifies the logarithmic coefficient using divergence of the reciprocal
prime series and proves the reverse implication in `ErdosX`.

## Arithmetic propositions and their proofs

[`AssemblyStatements.lean`](Erdos1122/AssemblyStatements.lean) records
named propositions about the actual functions in the manuscript. These
names make the dependencies inspectable; all are discharged before the
main theorem is applied.

| Proposition | Proved implication | Source |
|---|---|---|
| `NormalizationExists` | `normalization_exists : NormalizationExists`; its definition takes `ErdosV` as input | [NormalizedExistence.lean](Erdos1122/NormalizedExistence.lean) |
| `Estimate55` | `estimate55_of_ruzsa : Ruzsa → Estimate55` | [MixedMoment.lean](Erdos1122/MixedMoment.lean) |
| `ClippedComparison` | `clipped_comparison : ClippedComparison`; its definition takes `Elliott` and `Estimate55` as inputs | [ClippedComparison.lean](Erdos1122/ClippedComparison.lean) |
| `ProjectionInstance` | `projection_instance : ProjectionInstance`; its definition takes `Ruzsa` as input | [VarianceLower.lean](Erdos1122/VarianceLower.lean) |
| `WindowAssembly` | `window_assembly_of_elliott : Elliott → WindowAssembly` | [WindowAssembly.lean](Erdos1122/WindowAssembly.lean) |

The normalization data include positive scales, `s_X → ∞`, `c_X → 0`,
the prescribed capped quadratic mass, and actual global minimizers.
[`Minimizer.lean`](Erdos1122/Minimizer.lean) proves continuity,
coercivity, attainment, breakpoint exclusion, and stationarity using
smooth quadratic branches touching the capped function from above.
[`Scale.lean`](Erdos1122/Scale.lean) supplies continuity in the scale,
monotonicity, and level attainment.
[`Normalization.lean`](Erdos1122/Normalization.lean) proves fixed-scale
divergence from `ErdosV` by compactness and bounded finite prime sums.
`NormalizedExistence` completes the slope limit: a fixed finite set of
primes with sufficiently large reciprocal mass excludes any slope bounded
away from zero.

[`ShortIntervalTheorem.lean`](Erdos1122/ShortIntervalTheorem.lean)
proves all of Lemma 2.1 from `Mangerel` and `Elliott`, including the
varying family `z_X`, real cutoffs, and the limit in `X` before the integer
limit in `H`. The dyadic cover, moment transfer, fourth-moment contraction,
and center errors are proved. In particular, the exact floor identity
(2.7) has error bounded by `2 L π(Y)/Y`, which tends to zero by
Chebyshev's prime-counting bound.
[`ComparisonFamily.lean`](Erdos1122/ComparisonFamily.lean) applies this
theorem to the manuscript's clipped prime-divisor family.

[`PrimeReciprocal.lean`](Erdos1122/PrimeReciprocal.lean),
[`PrimeMoment.lean`](Erdos1122/PrimeMoment.lean), and
[`PrimeHarmonic.lean`](Erdos1122/PrimeHarmonic.lean) prove Lemma 3.1
without an external analytic input. Chebyshev and Abel summation give

\[
 \sum_{y<p\le X}\frac1p
 \le \log4\left(\log\frac{\log X}{\log y}+\frac1{\log y}\right),
 \qquad 2\le y\le X.
\]

The resulting tail bound is `C M log(2/M) + log(4)/log X`, with an
absolute `C`. `M` is fixed before the cutoff, and the estimate is uniform
over all eligible prime sets. No Mertens hypothesis remains.
[`PrimeLogSquare.lean`](Erdos1122/PrimeLogSquare.lean) also derives

\[
 \sum_{p\le X}(\log p)^2/p\ge(\log2/8)(\log X)^2
\]

for sufficiently large `X`, using mathlib's `Chebyshev.theta_ge'` and
Abel summation. This lower bound suffices for (5.10).

`MixedMoment` proves (5.5) by reindexing the multiples of each tail prime,
applying the Ruzsa upper bound at the smaller real scale, and bounding
the change of center by Cauchy–Schwarz. The prime-tail estimate supplies
the stated dependence on `M`.
[`FiniteCounting.lean`](Erdos1122/FiniteCounting.lean) supplies the
indicator union bound and `E[T(T-1)] ≤ M²`.
[`AdditiveExpansion.lean`](Erdos1122/AdditiveExpansion.lean) proves
`f(n) = Σ_{p|n} f(p^{v_p(n)})` for every positive integer, and the exact
higher-prime-power difference of the two arguments **before clipping**.
[`HigherPowerComparison.lean`](Erdos1122/HigherPowerComparison.lean)
uses the existing higher-prime-power union bound to prove
`E_X |Y-Y_*|² → 0`, with arbitrary moving centers. `ClippedComparison`
then combines the zero-, one-, and multiple-tail cases with the moments.

[`PrimeProjection.lean`](Erdos1122/PrimeProjection.lean) applies the
finite projection to the actual normalized prime values. Its lower
expression is

\[
 M-c_X^2-\frac8{\log2}
   \left(\frac{|c_X|}{\log X}+KM\right)^2,
\]

uniformly over the real projection coefficient. It tends to
`M - (8/log 2) K² M²`.
[`MovingCenters.lean`](Erdos1122/MovingCenters.lean) proves convergence
of Ruzsa's center to the prime center using a summable `4K/p²` majorant.
`VarianceLower` retains the exponent-one terms in Ruzsa's actual infimum
and completes Lemma 5.2.

[`ObservableVariation.lean`](Erdos1122/ObservableVariation.lean)
uses the actual decrease count to prove small total variation and
vanishing backward-window discrepancy of `Y`. `WindowAssembly` proves
the four-term comparison, Jensen contraction, and the vanishing finite
prefix. It takes `X → ∞` at fixed `H`, then `H → ∞`.
[`Constants.lean`](Erdos1122/Constants.lean) chooses `K` and `M`
before either estimate is instantiated.
Finally, [`ConcentrationConclusion.lean`](Erdos1122/ConcentrationConclusion.lean)
proves that the limiting distribution has no negative mass and that the
resulting logarithmic coefficient is nonnegative.

## Reproducing the checks

The project pins Lean 4.33.0 and mathlib v4.33.0;
`lake-manifest.json` fixes the dependency revisions. Run:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1122
```

[`Check.lean`](Check.lean) checks both the exact input type of
`main_of_cited` and the axiom dependencies of the main theorem and its
arithmetic components. The permitted dependencies are `propext`,
`Classical.choice`, and `Quot.sound`. There are no admitted proofs,
additional axiom declarations, or uses of `native_decide`.

The executable name is correct for the pinned Lean version:
[the official lean4checker repository](https://github.com/leanprover/lean4checker)
states that it was merged into Lean 4.28.0 and is distributed as
`leanchecker`. No archived Lake dependency is needed. The
[builtin source at v4.33.0](https://github.com/leanprover/lean4/blob/v4.33.0/src/LeanChecker.lean)
replays declarations with the Lean kernel. This is an additional check
of the compiled declarations, not an independently implemented kernel.
The command above checks the project's `Erdos1122` modules over their
imported environments; it does not request fresh replay of every mathlib
dependency. The GitHub Actions workflow runs all three checks.

## AI disclosure

OpenAI Codex (GPT-6) generated the Lean code and its documentation. Lean
checked the proof terms. This disclosure concerns the formalization; the
manuscript separately records its mathematical and editorial preparation.
