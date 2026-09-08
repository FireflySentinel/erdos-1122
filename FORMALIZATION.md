# Lean formalization

This repository contains Lean proofs of the finite inequalities used in the
manuscript. **It does not contain a Lean proof of the full Erdős Problem 1122.**
The source files prove the statements below for arbitrary real inputs and
finite sets; no numerical sampling is involved.

## What is proved

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

The present files do not formalize the Erdős concentration and difference
distribution theorems, the Ruzsa and Elliott moment estimates, Mangerel's
short-interval theorem, or the prime-sum estimates. They also do not formalize
the truncated minimizer construction, the mixed moment over tail primes,
the higher-prime-power convergence argument, or the assembly of all the
asymptotic steps into the main theorem. These remain mathematical arguments
in [`paper/PROOF.pdf`](paper/PROOF.pdf).

None of these omitted results is introduced into Lean as an axiom or as a
theorem with an admitted proof.

## Reproducing the checks

The project pins Lean 4.33.0 and mathlib v4.33.0. `lake-manifest.json` fixes
the dependency revisions. With [elan](https://github.com/leanprover/elan)
installed, run from the repository root:

```sh
lake exe cache get Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Data.Real.Basic Mathlib.Tactic
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
