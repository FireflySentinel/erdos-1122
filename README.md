# Erdős Problem #1122: additive functions that decrease on a density-zero set

Preprint answering [Erdős Problem #1122](https://www.erdosproblems.com/1122) in the
affirmative. Mangerel [[Ma22](https://arxiv.org/abs/2108.12351)] proved the conclusion
under the stronger bound $\lvert A\cap[1,X]\rvert\ll X/(\log X)^{2+c}$ together with a
technical condition on the values $f(p)$. Both extra hypotheses are removed here, and the
constant is shown to be nonnegative.

## Exact statement

**Theorem 1.** Let $f\colon\mathbb N\to\mathbb R$ be additive. If

$$D_f(X) := \#\{n \le X : f(n+1) < f(n)\} = o(X),$$

then there is a constant $c\ge0$ such that $f(n)=c\log n$ for every $n\in\mathbb N$.

No restriction is placed on the values of $f$ at higher prime powers.

## Method

Two results of Erdős reduce the theorem to *finite concentration*: that some interval of
a fixed length holds a positive proportion of the values $f(n)$, $n\le X$, for arbitrarily
large $X$. Assume this fails. Normalizing $f$ and subtracting a logarithm makes the
truncated quadratic mass of the prime values equal to a small fixed $M$, and the
minimizing logarithmic coefficient gives an orthogonality identity. A bounded clipping of
the normalized function is then compared with the strongly additive function obtained by
clipping its prime values: their mean-square difference is small enough for the clipped
function to keep a positive variance, while the density hypothesis makes it almost
constant on a typical interval of any fixed length. Mangerel's first-moment theorem for
short intervals, with the moment estimates of Ruzsa and Hildebrand, then forces a variance
smaller than the moment lower bound permits.

## Contents

The manuscript is `paper/PROOF.tex`, compiled to `paper/PROOF.pdf`.
This preprint carries no Lean formalization.

## Use of generative AI

The proofs and the first draft were generated with GPT-6 Astra through Codex; a separate
instance of the same model reviewed the arguments and their use of the cited results.
The author checked the arguments and is responsible for the content.
