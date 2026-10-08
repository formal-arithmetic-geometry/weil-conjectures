+++
id = "lemma-nagata-chart-generators-associated"
kind = "lemma"
title = "Transition between local exceptional generators"
order = 95
lean = ["AlgebraicGeometry.AffineBlowup.exists_units_awayAlgebraMap_eq_mul"]
uses = ["def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-chart-extended-ideal-principal", "lemma-nagata-chart-generator-regular", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
On the overlap of the $a$-chart and the $b$-chart, the two generators $a$
and $b$ of the extended ideal differ by a unit.

## Proof

On the overlap, both $(a)$ and $(b)$ equal the same extended ideal. More
explicitly, $b=a(b/a)$ and $a=b(a/b)$, and $(a/b)(b/a)=1$.
