+++
id = "lemma-nagata-chart-extended-ideal-principal"
kind = "lemma"
title = "Principalization on one affine chart"
order = 93
lean = ["AlgebraicGeometry.AffineBlowup.map_awayAlgebraMap_eq_span_singleton"]
uses = ["def-nagata-blowup-chart-ring", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
In $A[I/a]$, the extended ideal satisfies

$$
I\,A[I/a]=(a).
$$

## Proof

For $x\in I$, the identity $x=a(x/a)$ gives
$IA[I/a]\subseteq(a)$. Since $a\in I$ and $1\in A[I/a]$, the element
$a=a\cdot1$ belongs to $IA[I/a]$, so every multiple of $a$ belongs to that
ideal and $(a)\subseteq IA[I/a]$.
