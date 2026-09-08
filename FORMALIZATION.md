# Formalized inputs

[`main_of_cited`](Erdos1122/Main.lean) proves
`Mangerel → Ruzsa → ErdosV → Hildebrand → ErdosProblem1122`.
The exact definitions are in [Statements.lean](Erdos1122/Statements.lean)
and [HildebrandStatements.lean](Erdos1122/HildebrandStatements.lean).

All arithmetic functions are real-valued on positive integers. Cutoffs `X` are real;
`Ioc a b` means `a < n ≤ b`. Initial and dyadic sums use `Ioc 0 ⌊X⌋₊` and
`Ioc ⌊X/2⌋₊ ⌊X⌋₊`, normalized by `1/X` and `2/X`, respectively.
Estimate constants are quantified before the function, cutoff, and window.

| Hypothesis | Source | Conventions and scope |
|---|---|---|
| `Mangerel` | [Theorem 1.1, p. 1026](https://doi.org/10.1007/s11139-022-00623-y) | Real specialization; integer window `10 ≤ H ≤ X/100`; backward mean over `n-H < m ≤ n`. The constant is uniform when the function varies with `X`. |
| `Ruzsa` | [Ruzsa (1983), pp. 577–586](https://doi.org/10.1007/978-3-0348-5438-2_50), as restated in Mangerel, Lemma 3.3, p. 1038 | Center `Σ f(p^k)(1-1/p)/p^k`; absolute `c, C, X₀`, with `X₀ ≥ 3`; the two-sided estimate is assumed for `X ≥ X₀`. The lower bound is used as `X → ∞`; [FiniteCutoffMoment.lean](Erdos1122/FiniteCutoffMoment.lean) extends the upper bound to smaller scales. Source comparison currently uses Mangerel's published restatement. |
| `ErdosV` | [Erdős (1946), Theorem V and the following converse, p. 3](https://combinatorica.hu/~p_erdos/1946-06.pdf) | Finite concentration iff `Σ_p min((f(p)-c log p)²,1)/p < ∞` for some real `c`; the concentrating interval can depend on `X`. |
| `Hildebrand` | [Hildebrand (1988), Theorem 1 and (1.4), pp. 257–258; corollary, pp. 258–259](https://doi.org/10.1090/S0002-9947-1988-0965752-X) | Only sufficiency of the prime summability condition is assumed, together with (1.4) for the resulting probability law. The Euler product is taken in increasing prime order. CDF convergence is at continuity points, with a right-continuous CDF; replacing `1/⌊X⌋` by `1/X` preserves the limit. The corollary uses an actual density-one set. |

The manuscript cites Elliott for the fourth moment and uses Mertens for shorter
prime-sum estimates. Lean proves the needed [fourth moment](Erdos1122/StrongFourthMoment.lean)
by finite expansion and divisor counting, and the [prime-tail estimate](Erdos1122/PrimeHarmonic.lean)
and [log-square lower bound](Erdos1122/PrimeLogSquare.lean) from mathlib's Chebyshev bounds.
These add no hypotheses to `main_of_cited`.
