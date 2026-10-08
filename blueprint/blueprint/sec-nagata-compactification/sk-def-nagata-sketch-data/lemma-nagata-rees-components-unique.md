+++
id = "lemma-nagata-rees-components-unique"
kind = "lemma"
title = "Uniqueness of the homogeneous decomposition"
order = 20
lean = ["AlgebraicGeometry.reesGrading_isInternal"]
uses = ["def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul"]
+++
Let $E$ be a finite set of pairwise distinct degrees and choose one element
$F_n\in\mathcal R_A(I)_n$ for each $n\in E$. If
$\sum_{n\in E}F_n=0$, then every $F_n$ is zero.

## Proof

Apply the coefficient projection in a fixed degree $n\in E$. Every summand
of degree different from $n$ has zero $n$th component, so the projection of
the displayed sum is $F_n=0$. This holds for every $n\in E$.
