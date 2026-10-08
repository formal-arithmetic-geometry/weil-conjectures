+++
id = "lem-exc-constant-tensor"
kind = "lemma"
title = "Constant coefficient tensor comparison"
order = 1912
uses = ["def-weil-derived-tensor", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image"]
+++
Let $A$ be a finite ring, and let $j$ be an open immersion. Suppose that
$Rj_*$ on the ordinary
derived categories of
etale $A$-module sheaves preserves countable coproducts.
For $K\in D(U_{\mathrm{et}},A)$ and a finite $A$-module $N$,
the canonical tensor comparison is
an isomorphism

$$
(Rj_*K)\otimes_A^L N_T
\longrightarrow Rj_*(K\otimes_A^L N_U).
$$

The symbols $N_T,N_U$ denote constant module sheaves.

## Proof

Since $A$ is Noetherian and $N$ is finite, successive finite free
covers of kernels give a resolution $P$ of $N$ by finite free
modules in degrees at most zero.
For every finite brutal truncation $P_{\geq-m}$, the comparison is
an isomorphism: it holds for $A$, for finite sums and shifts, and
then for finite complexes by the triangle for adjoining one term.
The natural inclusions $P_{\geq-m}\to P_{\geq-m-1}$ have homotopy
colimit $P$. In the ordinary derived categories of
[def-weil-pbc-derived-categories], this homotopy colimit is the
cone of $1-\mathrm{shift}$ on the countable direct sum, with its
usual quasi-isomorphism to the degreewise filtered colimit.
Derived tensor of [def-weil-derived-tensor] and the assumed
coproduct-preserving $Rj_*$ preserve this triangle. Passing to the
homotopy colimit proves the comparison.

This argument uses finite free terms and a countable sequence of
truncations. It does not require that $N$ have finite projective
dimension.
