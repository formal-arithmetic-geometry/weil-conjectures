+++
id = "lem-weil-scalar-extension-well-defined"
kind = "lemma"
title = "Well-definedness of scalar extension"
order = 1882
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-derived-tensor", "def-weil-rationalization-karoubi", "prop-weil-pbc-rational-transport"]
+++
Let $E\subset L$ be a finite extension of $\Ql$, with rings of integers
$\mathcal O_E\subset\mathcal O_L$ and uniformizers $\varpi_E,\varpi_L$, and
let $Y$ be a scheme. For an object of the rationalized category $D^b_c(Y,E)$
of [def-weil-rationalization-karoubi] represented by an integral complex
$K\in D^b_c(Y,\mathcal O_E)$, the object

$$
 \bigl(K\otimes^L_{\mathcal O_E}\mathcal O_L\bigr)
 \otimes_{\mathcal O_L}L
$$

of $D^b_c(Y,L)$, formed with the derived tensor product
[def-weil-derived-tensor], levelwise modulo powers of the two uniformizers
and followed by rationalization, is independent of the chosen integral
representative $K$, up to canonical isomorphism.

## Proof

The composite of the functor $-\otimes^L_{\mathcal O_E}\mathcal O_L$, the
levelwise reductions and the rationalization is $\mathcal O_E$-linear and
exact on the derived-complete integral constructible category
$D^b_c(Y,\mathcal O_E)$ of [def-weil-derived-complete-integral-detailed]:
$\mathcal O_L$ is finite free over $\mathcal O_E$, so tensoring with it
preserves the boundedness and the derived completeness of the objects, and
the derived tensor product used at each stage is that of
[def-weil-derived-tensor]. By the rational-transport proposition of the
proper-base-change chapter every exact $\mathcal O_E$-linear functor on the
integral constructible category extends uniquely to its rationalization
$D^b_c(Y,E)$ of [def-weil-rationalization-karoubi], and a uniquely determined
extension is computed indifferently from any integral representative of its
argument.
