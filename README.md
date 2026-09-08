# Erdős Problem #1122

[Preprint](paper/PROOF.pdf) · [TeX](paper/PROOF.tex) · [Problem](https://www.erdosproblems.com/1122)

**Theorem 1.1.** Let $f\colon\mathbb N\to\mathbb R$ be additive. If
$D_f(X)=\#\{n\le X:f(n+1)<f(n)\}=o(X)$, then $f(n)=c\log n$ for every
positive integer $n$, for some $c\ge0$.

The Lean 4 theorem has the type

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

[FORMALIZATION.md](FORMALIZATION.md) records the source conventions.
The strongly additive [fourth moment](Erdos1122/StrongFourthMoment.lean) is proved
by finite expansion and counting multiples; the prime-sum estimates follow from
mathlib's Chebyshev bounds. The paper uses Elliott and Mertens for brevity, while
Lean needs neither as an input. [HildebrandBridge.lean](Erdos1122/HildebrandBridge.lean)
proves the symmetry argument and the required consequence of Erdős's Theorem X.

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root
(`lake exe cache get` downloads the optional mathlib build cache):

```sh
lake build
lake env lean -DwarningAsError=true Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos1122
```

CI runs all three commands. [Check.lean](Check.lean) fixes the main theorem's type
and guards its transitive axiom dependencies to `propext`, `Classical.choice`, and
`Quot.sound`; `leanchecker` replays the declarations with the Lean kernel.

The cited theorems' proofs and the correspondence between their source statements
and the Lean hypotheses remain for human review. Lean checks the full implication
from those hypotheses; it does not check the TeX exposition.

GPT-6 Astra generated proofs and manuscript drafts, GPT-5.6 Sol and Claude Opus 5
assisted with editorial review, and OpenAI Codex (GPT-6) generated the Lean code.
