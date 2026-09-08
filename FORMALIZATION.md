# Lean formalization

This repository formalizes parts of the manuscript, including the finite
minimization, the ordered limiting arguments, and a conditional proof of
Lemma 3.1. **It does not contain a Lean proof of the full Erdős Problem 1122.**
Cited analytic results enter as explicit theorem hypotheses. No numerical
sampling is involved.

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

- [`PrimeHarmonic.lean`](Erdos1122/PrimeHarmonic.lean), together with
  [`PrimeTail.lean`](Erdos1122/PrimeTail.lean) and
  [`PrimeMoment.lean`](Erdos1122/PrimeMoment.lean), proves Lemma 3.1
  conditional on the following precise Mertens and Chebyshev bounds:

  $$\left|\sum_{p\le y}\frac1p-\log\log y-B\right|
       \le\frac A{\log y},\qquad
    \vartheta(y)\le Dy\quad(y\ge2),\qquad A,D\ge0.$$

  The code proves the Abel partial-summation identity for
  $\sum_{p\le y}(\log p)/p$, the local prime-harmonic estimates, and the
  finite sum interchange. It obtains

  $$\sum_{p\in T}\frac1p\sum_{X/p<q\le X}\frac1q
     \le C M\log(2/M)+\frac{A(M+1)}{\log X},$$

  where

  $$C=1+\frac{(2+3A/\log2)D(1+1/\log2)}{\log2}.$$

  Here $0<M<1/4$, $X\ge2$, $X^M\ge2$, and
  $\sum_{p\in T}1/p\le M$. The theorem `primeTailKernel_eventually`
  fixes $M$ before the eventual threshold in $X$ and is uniform over $T$.
  The error is separately proved to tend to zero. The constant $C$ is
  independent of $M$, $X$, and $T$.

- [`ShortIntervals.lean`](Erdos1122/ShortIntervals.lean) proves the
  first-to-second-moment transfer for arrays depending on both $H$ and $X$.
  The input first-moment bound has the explicit form $a(H)+b(X)$, with
  both errors tending to zero, and the fourth-moment bound is uniform in
  the array. It also proves the initial-segment estimate
  $\sum_S w_i f_i^2\le\sqrt{\eta C}$ from mass at most $\eta$ and fourth
  moment at most $C$, and the assembly from finitely many bands.

  This verifies the analytic transfer and limit operations in Lemma 2.1.
  It is not yet a complete formalization of that lemma: identifying the
  arrays with Mangerel's short averages, proving the particular dyadic
  cover, and deriving the center-error limits remain outside Lean.
  Those inputs are visible hypotheses of the assembly theorem.

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

- [`Averaging.lean`](Erdos1122/Averaging.lean) proves finite mean-square
  contraction, the four-term comparison, and the identity expressing total
  variation in terms of negative increments and the endpoint difference.

- [`Variation.lean`](Erdos1122/Variation.lean) proves the quantitative estimate

  $$
  \sum_{n<N}|Y(n)-A_HY(n)|^2
  \le 2KH\sum_{m<N+H}|Y(m+1)-Y(m)|,
  $$

  for positive integer $H$ and $|Y(m)|\le K$ on $m<N+H$.
  Here $A_H$ uses forward windows. Reindexing gives the backward-window
  convention of the manuscript. The estimate supplies the finite inequality
  behind its passage from small total variation to small window discrepancy.

## What remains outside Lean

The Erdős concentration and difference-distribution theorems, the Ruzsa
and Elliott moment estimates, and Mangerel's theorem are not proved here.
The Mertens bound is a hypothesis of the conditional prime-tail result.
The varying-scale construction of $s_X,c_X$ in Lemma 4.1, its convergence
arguments, the mixed moment over tail primes, the remaining arithmetic
steps of Lemma 2.1, and the instantiation of the final variance comparison
for the manuscript's functions remain outside Lean. These are arguments
in [`paper/PROOF.pdf`](paper/PROOF.pdf).

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
