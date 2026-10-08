+++
id = "lemma-nagata-rees-degree-one-element"
kind = "lemma"
title = "Degree-one element associated to an ideal element"
order = 23
lean = ["AlgebraicGeometry.reesX"]
uses = ["def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-piece-membership"]
+++
Every $a\in I$ determines a homogeneous element $at$ of degree one. Its
underlying polynomial and its coefficient in degree one are recorded by
simp lemmas.

## Proof

Since $a\in I=I^1$, the monomial $at$ belongs to the degree-one piece by
[lemma-nagata-rees-piece-membership]. The underlying-polynomial and
coefficient formulas follow from the corresponding formulas for a
polynomial monomial.
