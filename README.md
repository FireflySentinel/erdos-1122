# Erdős Problem #1122: additive functions monotone off a density-zero set

[Preprint](paper/PROOF.pdf) on [Erdős Problem #1122](https://www.erdosproblems.com/1122),
answering it in the affirmative for every additive function. Mangerel
[[Ma22](https://arxiv.org/abs/2108.12351)] obtained the exact conclusion under the stronger
bound $D_f(X)\ll X/(\log X)^{2+c}$ together with a technical condition on the values
$f(p)$; both extra hypotheses are removed here, and the constant is shown to be
nonnegative.

Two results of Erdős reduce the theorem to *finite concentration*: some interval of a
fixed length holds a positive proportion of the values $f(n)$, $n\le X$, for arbitrarily
large $X$. Ruzsa's second-moment estimate and Elliott's high-power Turán–Kubilius
inequality give a positive variance for a clipped strongly additive comparison, while the
density hypothesis and Mangerel's first-moment theorem for short intervals force the same
variance to vanish.

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

This is a partial formalization: Theorem 1.1 itself is not proved in Lean. The cited
analytic results enter as explicit hypotheses of the formalized statements.
[FORMALIZATION.md](FORMALIZATION.md) states those hypotheses and lists what remains
outside Lean. Lemma 3.1 is unconditional, using Chebyshev’s bound from mathlib.
Lemma 2.1 is proved with Mangerel and Elliott as its only external inputs. [Check.lean](Check.lean) guards the axiom dependencies of the formalized
lemmas to `propext`, `Classical.choice`, and `Quot.sound`.

## Proof correspondence

| Manuscript | Lean source |
|---|---|
| Theorem 1.1 and the five cited inputs: proposition definitions and unproved assembly target | [Statements.lean](Erdos1122/Statements.lean) |
| Lemma 2.1 in full, conditional on Mangerel and Elliott | [ShortIntervalTheorem.lean](Erdos1122/ShortIntervalTheorem.lean), [DyadicShortIntervals.lean](Erdos1122/DyadicShortIntervals.lean), [DyadicCover.lean](Erdos1122/DyadicCover.lean) |
| Lemma 2.1, first- and fourth-moment interpolation | [Interpolation.lean](Erdos1122/Interpolation.lean) |
| Lemma 3.1, unconditional prime-tail weight | [PrimeHarmonic.lean](Erdos1122/PrimeHarmonic.lean), [PrimeReciprocal.lean](Erdos1122/PrimeReciprocal.lean), [PrimeMoment.lean](Erdos1122/PrimeMoment.lean) |
| Lemma 4.1, finite minimizer and the stationary identity | [Minimizer.lean](Erdos1122/Minimizer.lean) |
| Lemma 4.1, scale continuity, monotonicity, and intermediate-value attainment | [Scale.lean](Erdos1122/Scale.lean) |
| Lemma 4.1, fixed-scale divergence and $s_X\to\infty$, conditional on Erdős V | [Normalization.lean](Erdos1122/Normalization.lean) |
| (2.7), exact floor identity; (5.4), prime-divisor factorial moment | [FiniteCounting.lean](Erdos1122/FiniteCounting.lean) |
| (2.8), fourth-power Jensen and window contraction | [Averaging.lean](Erdos1122/Averaging.lean) |
| §5, weighted quadratic projection and its lower bound | [Projection.lean](Erdos1122/Projection.lean) |
| §5, clipping bounds and the finite tail error | [Clipping.lean](Erdos1122/Clipping.lean) |
| §5, union bound over higher prime powers | [PrimePowers.lean](Erdos1122/PrimePowers.lean) |
| §6, forward and backward window discrepancy from total variation | [Variation.lean](Erdos1122/Variation.lean), [Averaging.lean](Erdos1122/Averaging.lean) |
| §6, ordered choice of $K$ and $M$, and the variance contradiction | [Constants.lean](Erdos1122/Constants.lean), [Limits.lean](Erdos1122/Limits.lean) |

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition.
The Lean formalization was generated using OpenAI Codex (GPT-6).
