# Erdős Problem #1122: additive functions monotone off a density-zero set

[Preprint](paper/PROOF.pdf) on [Erdős Problem #1122](https://www.erdosproblems.com/1122),
answering it in the affirmative for every additive function. Mangerel
[[Ma22](https://arxiv.org/abs/2108.12351)] obtained the exact conclusion under the stronger
bound $D_f(X)\ll X/(\log X)^{2+c}$ together with a technical condition on the values
$f(p)$; both extra hypotheses are removed here, and the constant is shown to be
nonnegative.

Results of Erdős and Hildebrand reduce the theorem to *finite concentration*: some interval of a
fixed length holds a positive proportion of the values $f(n)$, $n\le X$, for arbitrarily
large $X$. Ruzsa's second-moment estimate and Elliott's high-power Turán–Kubilius
inequality give a positive variance for a clipped strongly additive comparison, while the
density hypothesis and Mangerel's first-moment theorem for short intervals force the same
variance to satisfy an incompatible upper bound.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1122
```

## Exact statement

**Theorem 1.1.** Let $f\colon\mathbb N\to\mathbb R$ be additive, and let $D_f(X)$ count
the $n\le X$ with $f(n+1)<f(n)$. If $D_f(X)=o(X)$, then there is a constant $c\ge0$ such
that $f(n)=c\log n$ for every $n\in\mathbb N$.

No restriction is placed on the values of $f$ at higher prime powers, and the set of
decreases is only assumed to have density zero, with no rate.

Lean proves the full implication from the cited analytic inputs to Theorem 1.1:
`main_of_cited` takes `Mangerel`, `Ruzsa`, `Elliott`, `ErdosV`, and `Hildebrand`
as hypotheses. No intermediate arithmetic hypothesis remains. The cited
theorems themselves are not proved in this repository.
[FORMALIZATION.md](FORMALIZATION.md) gives their exact scope and source
conventions. `Hildebrand` consists of his 1988 Theorem 1, including its
characteristic-function formula, and its density-one corollary. The bridge
`hildebrand_implies_erdosX` is proved; Erdős’s unproved announcement is no
longer an external input. Ruzsa is assumed only above an absolute cutoff,
with the small-scale upper bound supplied by a finite Cauchy estimate.
Lemma 3.1 and the prime-sum lower bound in (5.10) use Chebyshev alone;
there is no Mertens input. [Check.lean](Check.lean) checks the complete
five-input interface and guards its axiom dependencies to `propext`,
`Classical.choice`, and `Quot.sound`. CI also runs the builtin Lean 4
`leanchecker` to replay the project declarations.

## Proof correspondence

| Manuscript | Lean source |
|---|---|
| Theorem 1.1 from the stated analytic inputs | [Main.lean](Erdos1122/Main.lean), [Statements.lean](Erdos1122/Statements.lean) |
| Hildebrand’s theorem and corollary imply the required Erdős X statement | [HildebrandStatements.lean](Erdos1122/HildebrandStatements.lean), [HildebrandBridge.lean](Erdos1122/HildebrandBridge.lean) |
| Finite-cutoff upper bound, without an extra analytic input | [FiniteCutoffMoment.lean](Erdos1122/FiniteCutoffMoment.lean) |
| Lemma 2.1 in full, conditional on Mangerel and Elliott | [ShortIntervalTheorem.lean](Erdos1122/ShortIntervalTheorem.lean), [DyadicShortIntervals.lean](Erdos1122/DyadicShortIntervals.lean), [DyadicCover.lean](Erdos1122/DyadicCover.lean) |
| Lemma 2.1, first- and fourth-moment interpolation | [Interpolation.lean](Erdos1122/Interpolation.lean) |
| Lemma 3.1, unconditional prime-tail weight | [PrimeHarmonic.lean](Erdos1122/PrimeHarmonic.lean), [PrimeReciprocal.lean](Erdos1122/PrimeReciprocal.lean), [PrimeMoment.lean](Erdos1122/PrimeMoment.lean) |
| Lemma 4.1, finite minimizer and the stationary identity | [Minimizer.lean](Erdos1122/Minimizer.lean) |
| Lemma 4.1, scale continuity, monotonicity, and intermediate-value attainment | [Scale.lean](Erdos1122/Scale.lean) |
| Lemma 4.1 in full, including $s_X\to\infty$ and $c_X\to0$, from Erdős V | [Normalization.lean](Erdos1122/Normalization.lean), [NormalizedExistence.lean](Erdos1122/NormalizedExistence.lean) |
| (2.7), exact floor identity; (5.4), prime-divisor factorial moment | [FiniteCounting.lean](Erdos1122/FiniteCounting.lean) |
| (2.8), fourth-power Jensen and window contraction | [Averaging.lean](Erdos1122/Averaging.lean) |
| Lemma 5.2, actual prime projection and Ruzsa variance lower bound | [PrimeProjection.lean](Erdos1122/PrimeProjection.lean), [VarianceLower.lean](Erdos1122/VarianceLower.lean) |
| (5.5), from Ruzsa; Lemma 5.1, complete clipping comparison | [MixedMoment.lean](Erdos1122/MixedMoment.lean), [ClippedComparison.lean](Erdos1122/ClippedComparison.lean) |
| §5, additive expansion and vanishing higher-prime-power comparison | [AdditiveExpansion.lean](Erdos1122/AdditiveExpansion.lean), [HigherPowerComparison.lean](Erdos1122/HigherPowerComparison.lean) |
| §6, density-zero decreases, total variation, and window assembly | [ObservableVariation.lean](Erdos1122/ObservableVariation.lean), [WindowAssembly.lean](Erdos1122/WindowAssembly.lean) |
| §6, ordered choice of $K$ and $M$, and the variance contradiction | [Constants.lean](Erdos1122/Constants.lean), [Limits.lean](Erdos1122/Limits.lean) |

The two cited moment centers and their conversion are proved in
[CenterShift.lean](Erdos1122/CenterShift.lean),
[SecondMoment.lean](Erdos1122/SecondMoment.lean), and
[MovingCenters.lean](Erdos1122/MovingCenters.lean).

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition.
The Lean formalization was generated using OpenAI Codex (GPT-6).
