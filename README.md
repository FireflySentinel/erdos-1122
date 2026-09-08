# Erdős Problem #1122: additive functions monotone off a density-zero set

Lean 4 formalization answering [Erdős Problem #1122](https://www.erdosproblems.com/1122)
in the affirmative: an additive function whose set of decreases has natural density zero
is $c\log n$ for a constant $c\ge0$. Four cited results enter as explicit hypotheses.

```lean
Erdos1122.Statements.main_of_cited :
  Mangerel → Ruzsa → ErdosV → Hildebrand → ErdosProblem1122
```

| Hypothesis | Cited result |
|---|---|
| `Mangerel` | [Theorem 1.1 (2022), p. 1026](https://doi.org/10.1007/s11139-022-00623-y): first moments in short intervals |
| `Ruzsa` | [Second-moment estimate (1983), pp. 577–586](https://doi.org/10.1007/978-3-0348-5438-2_50), via Mangerel, Lemma 3.3, p. 1038 |
| `ErdosV` | [Theorem V and its converse (1946), p. 3](https://combinatorica.hu/~p_erdos/1946-06.pdf): finite concentration |
| `Hildebrand` | [Theorem 1, formula (1.4), and corollary (1988), pp. 257–259](https://doi.org/10.1090/S0002-9947-1988-0965752-X): the sufficient convergence criterion, characteristic function, and density-one rigidity |

The cited theorems themselves, and the correspondence between their source statements and
the Lean hypotheses, remain for human review.

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1122
```

CI runs the same checks. [Check.lean](Check.lean) fixes the main theorem's type and guards
its transitive axiom dependencies to `propext`, `Classical.choice`, and `Quot.sound`;
`leanchecker` replays the declarations with the Lean kernel.

## Proof correspondence

[FORMALIZATION.md](FORMALIZATION.md) records the source conventions.
The strongly additive [fourth moment](Erdos1122/StrongFourthMoment.lean) is proved by
finite expansion and counting multiples, and the prime-sum estimates follow from mathlib's
Chebyshev bounds, so the manuscript's appeals to Elliott and Mertens are not Lean inputs.
[HildebrandBridge.lean](Erdos1122/HildebrandBridge.lean) proves the symmetry argument and
the required consequence of Erdős's Theorem X.

## Use of generative AI

GPT-6 Astra proposed the argument and drafted the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used for editorial review.
The Lean formalization was generated with OpenAI Codex (GPT-6).
