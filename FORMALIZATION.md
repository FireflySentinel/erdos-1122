# Lean formalization

This repository formalizes parts of the manuscript, including the finite
minimization, Lemma 2.1 conditional on its two cited inputs, and an
unconditional proof of Lemma 3.1. **It does not contain a Lean proof of the full Erdős Problem 1122.**
Cited analytic results enter as explicit theorem hypotheses. No numerical
sampling is involved.

## Problem and cited statements

[`Statements.lean`](Erdos1122/Statements.lean) defines the original problem,
including coprime additivity on positive integers, the count $D_f(X)$, its
density-zero hypothesis, and the conclusion $f(n)=c\log n$ with $c\ge0$.
It also defines the real-valued forms of the five cited inputs:

- `Mangerel`: Theorem 1.1, with an absolute constant quantified before
  the function, real cutoff $X$, and integer window $10\le H\le X/100$.
- `Ruzsa`: the two-sided second-moment estimate recorded in Mangerel,
  Lemma 3.3 (Lemma 2.3 in arXiv v1), with center $A_0$.
- `Elliott`: Theorem 1 at exponent four, with its original center
  $\widetilde A_0$, without the factor $1-1/p$.
- `ErdosV`: finite concentration and its equivalent truncated prime sum,
  from Theorem V and the converse in the following paragraph.
- `ErdosX`: existence of the limiting difference distribution and its
  negative-support characterization, the parts of Theorem X used here.
  Empirical distributions converge at continuity points, using the standard
  right-continuous distribution convention. No condition on higher prime
  powers has been added.

The assembly target is explicitly defined as

```lean
main_of_cited : Prop :=
  Mangerel → Ruzsa → Elliott → ErdosV → ErdosX → ErdosProblem1122
```

These are definitions of propositions, not proofs of them. In particular,
`main_of_cited` is not a proved theorem. The prime-tail lemma has no
external analytic hypothesis; neither a Mertens proposition nor an
additional Mertens assembly target is needed.

## What is proved

- [`Minimizer.lean`](Erdos1122/Minimizer.lean) proves the finite-dimensional
  core of Lemma 4.1. For

  $$G(c)=c^2+\sum_{i\in T}w_i\min\{(a_i-c\ell_i)^2,1\},$$

  nonnegative weights give continuity, coercivity, and an attained global
  minimum. At any local minimum, a term with positive weight and nonzero
  slope cannot satisfy $|a_i-c\ell_i|=1$. The stationary identity is

  $$\sum_{\substack{i\in T\\|a_i-c\ell_i|<1}}
       w_i(a_i-c\ell_i)\ell_i=c.$$

  The proof uses smooth quadratic branches that lie above $G$ and agree
  with it at the minimum. Each such branch must also have a local minimum.
  At a breakpoint, selecting the quadratic or constant term gives two
  branches whose derivatives differ by a nonzero quantity, contradicting
  Fermat's theorem. Thus the argument never differentiates $G$ at an
  unverified smooth point. The original weights $1/p$ and slopes $\log p$
  satisfy the positivity and nonzero-slope conditions.

- [`Scale.lean`](Erdos1122/Scale.lean) proves that the minimum of
  $c^2+\sum_i w_i\min\{(a_i/s-c\ell_i)^2,1\}$ is continuous and
  nonincreasing for $s>0$, and tends to zero as $s\to\infty$.
  If its value at $s_0>0$ exceeds $M>0$, it attains $M$ at some $s>s_0$.
  The proof confines all minimizers to one compact interval independent
  of $s$.

  [`Normalization.lean`](Erdos1122/Normalization.lean) supplies the actual
  fixed-scale divergence $W_X(s)\to\infty$ for every $s>0$, from
  `Statements.ErdosV`, additivity, and failure of finite concentration.
  If the minima were bounded, nested compact sublevel sets would have a
  common point. At that point every finite prime sum is bounded, giving
  summability and contradicting Erdős V after rescaling. The file also
  proves eventual attainment of each fixed mass $M>0$ and that any
  positive scales satisfying $W_X(s_X)=M$ eventually tend to infinity.

- [`Constants.lean`](Erdos1122/Constants.lean) proves that, given
  $c_0>0$ and arbitrary real $C_0,C_1$, one can first fix $K>1$ so that
  every sufficiently small positive $M<1/4$ satisfies

  $$\frac{C_1M}{K^2}+C_1M^2\log(2/M)+C_1K^2M^2
       <c_0M-C_0K^2M^2.$$

  [`Limits.lean`](Erdos1122/Limits.lean) proves the four-term variance
  comparison with $X\to\infty$ followed by $H\to\infty$, the subsequent
  small-tail limit, and the contradiction from the final upper and lower
  variance bounds. Boundedness assumptions for real-valued limsups are
  explicit. No uniform rate in a varying $H$ or tail parameter is assumed.

- [`PrimeHarmonic.lean`](Erdos1122/PrimeHarmonic.lean) proves Lemma 3.1
  **without an external analytic hypothesis**. In
  [`PrimeReciprocal.lean`](Erdos1122/PrimeReciprocal.lean), Abel summation
  and mathlib's `Chebyshev.theta_le_log4_mul_x` give

  $$P(z)-P(y)\le D\left(\log\frac{\log z}{\log y}
      +\frac1{\log y}\right),\qquad 2\le y\le z,\quad D=\log4.$$

  [`PrimeMoment.lean`](Erdos1122/PrimeMoment.lean) supplies the logarithmic
  prime moment, and [`PrimeTail.lean`](Erdos1122/PrimeTail.lean) supplies
  the finite sum interchange. The resulting bound is

  $$\sum_{p\in T}\frac1p\sum_{X/p<q\le X}\frac1q
     \le C M\log(2/M)+\frac D{\log X},$$

  where

  $$C=D+\frac{(2+2/\log2)D^2(1+1/\log2)}{\log2}.$$

  Here $0<M<1/4$, $X\ge2$, $X^M\ge2$, and
  $\sum_{p\in T}1/p\le M$. The theorem `primeTailKernel_eventually`
  fixes $M$ before the eventual threshold in $X$ and is uniform over $T$.
  The error tends to zero. The constant $C$ is independent of $M$, $X$,
  and $T$. No Mertens estimate is used.

- [`ShortIntervalTheorem.lean`](Erdos1122/ShortIntervalTheorem.lean)
  proves **all of Lemma 2.1**, conditional only on `Statements.Mangerel`
  and `Statements.Elliott`. The theorem `lemma_2_1` permits a family
  $z_X$ of strongly additive functions indexed by real $X$, with fixed
  bounds $|z_X(p)|\le L$ and $\sum_{p\le X}|z_X(p)|^2/p\le V$. Its
  conclusion is

  $$\lim_{H\to\infty}\limsup_{X\to\infty}
    \frac1X\sum_{H\le n\le X}
      |\mathcal A_Hz_X(n)-\mu_{z_X}(X)|^2=0,$$

  with integer $H$ and real $X$. Both cited constants are quantified
  before the function family. The theorem assumes no rate uniform in
  $H$, no dyadic covering assertion, and no center-error limit.

  [`StrongAdditive.lean`](Erdos1122/StrongAdditive.lean) identifies
  strongly additive functions with their prime-divisor sums and proves
  the exact dyadic center identity. [`CenterErrors.lean`](Erdos1122/CenterErrors.lean)
  bounds that error by $2L\pi(Y)/Y$ and proves its convergence using
  mathlib's prime-counting bound. It also proves the change of prime
  center tends to zero on each fixed proportional interval.
  [`PrimePowerCenter.lean`](Erdos1122/PrimePowerCenter.lean) derives a
  uniform fourth moment from Elliott with its original unweighted
  prime-power center. [`BackwardMoments.lean`](Erdos1122/BackwardMoments.lean)
  proves contraction on the actual positive-index backward windows.

  [`DyadicShortIntervals.lean`](Erdos1122/DyadicShortIntervals.lean)
  applies Mangerel and the moment transfer on each fixed dyadic band.
  [`DyadicCover.lean`](Erdos1122/DyadicCover.lean) proves the finite
  covering and the $\sqrt{\eta C}$ initial-segment bound. The final
  theorem fixes the finite cover before taking either limit, then lets
  the initial-segment proportion tend to zero. Both `Statements` and
  `Variation` use the same `backwardWindowAverage` definition.

- [`FiniteCounting.lean`](Erdos1122/FiniteCounting.lean) proves the exact
  floor-counting identity (2.7), for real as well as integer cutoffs.
  It also proves

  $$\mathbb E_X[T(T-1)]\le M^2,\qquad
    \mathbf1_{T(n)\ge1}\le\sum_{p\in\mathcal T}\mathbf1_{p\mid n},$$

  where $T(n)$ counts the primes of $\mathcal T$ dividing $n$ and
  $\sum_{p\in\mathcal T}1/p\le M$. The factorial-moment bound counts
  multiples of products of distinct primes; it assumes no independence.

- [`PrimePowers.lean`](Erdos1122/PrimePowers.lean) proves

  $$\#\{1\le n\le X:\exists(p,k)\notin F,\ p\text{ prime},\ k\ge2,
       \ p^k\mid n\}
       \le X\sum_{\substack{(p,k)\notin F\\p\text{ prime},\ k\ge2}}p^{-k}.$$

  It proves convergence of the reciprocal sum by comparison with a product
  of a geometric series and a $p$-series. Convergence is therefore not an
  extra hypothesis of this theorem. The underlying finite and infinite
  divisor union bounds are also formalized.

- [`Clipping.lean`](Erdos1122/Clipping.lean) proves monotonicity and the Lipschitz
  bound for clipping, retention of truncated quadratic mass, and the error
  estimates for zero, one, and multiple tail terms. The theorem
  `clip_finite_tail_error_sq` combines these cases:

  $$
  \left|\phi_K\!\left(s+\sum_{i\in T}u_i\right)
       -s-\sum_{i\in T}\phi_K(u_i)\right|^2
  \le \frac{s^4}{K^2}+4s^2\mathbf 1_{T\ne\varnothing}
       +9K^2|T|(|T|-1),\qquad K>0.
  $$

- [`Projection.lean`](Erdos1122/Projection.lean) proves the weighted quadratic
  projection identity, attains its global minimum at the stated coefficient,
  and derives the lower bound from mass and correlation bounds. This is the
  finite-dimensional projection in the manuscript's variance lower bound.

- [`Interpolation.lean`](Erdos1122/Interpolation.lean) proves

  $$
  \left(\sum_i w_i a_i^2\right)^3
  \le \left(\sum_i w_i|a_i|\right)^2\sum_i w_i a_i^4,
  \qquad w_i\ge0.
  $$

  This is the polynomial form of the first- and fourth-moment interpolation
  used in Lemma 2.1.

- [`Averaging.lean`](Erdos1122/Averaging.lean) proves finite mean-square and
  fourth-power Jensen inequalities and window contractions, including the
  Jensen step in (2.8), the four-term comparison, and the identity expressing total
  variation in terms of negative increments and the endpoint difference.

- [`Variation.lean`](Erdos1122/Variation.lean) proves the quantitative estimate

  $$
  \sum_{n<N}|Y(n)-A_HY(n)|^2
  \le 2KH\sum_{m<N+H}|Y(m+1)-Y(m)|,
  $$

  for positive integer $H$ and $|Y(m)|\le K$ on $m<N+H$.
  Here $A_H$ uses forward windows. The file also proves the reflection
  identity and the backward-window bound, with the same constant, on
  exactly the indices $H,\ldots,H+N-1$. The estimate supplies the finite inequality
  behind its passage from small total variation to small window discrepancy.

## What remains outside Lean

The Erdős concentration and difference-distribution theorems, the Ruzsa
and Elliott moment estimates, and Mangerel's theorem are not proved here.
The convergence $c_X\to0$ in Lemma 4.1, the mixed moment over tail primes,
and the instantiation of the final variance comparison for the manuscript's
functions remain outside Lean. So does the final deduction of Theorem 1.1
from finite concentration and the difference distribution. These are arguments
in [`paper/PROOF.pdf`](paper/PROOF.pdf). The target remains `main_of_cited`,
with exactly the five cited inputs displayed above.

No omitted result is introduced as an axiom or as a theorem with an
admitted proof. A theorem that takes an analytic estimate as a hypothesis
proves only the stated implication; an axiom report does not certify
the truth of that hypothesis.

## Reproducing the checks

The project pins Lean 4.33.0 and mathlib v4.33.0. `lake-manifest.json` fixes
the dependency revisions. With [elan](https://github.com/leanprover/elan)
installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Check.lean
```

[`Check.lean`](Check.lean) checks the axiom dependencies of the main formalized
lemmas. Their permitted dependencies are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The source uses no `sorry`, `admit`,
`native_decide`, or additional axioms. The GitHub Actions workflow builds
the project and repeats the dependency checks.

## AI disclosure

GPT-6 Astra generated the Lean code and its documentation. Lean checked the
proof terms. This disclosure concerns the formalization; the manuscript's
separate disclosure records its mathematical and editorial preparation.
