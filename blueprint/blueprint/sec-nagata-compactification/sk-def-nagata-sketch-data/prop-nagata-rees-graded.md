+++
id = "prop-nagata-rees-graded"
kind = "theorem"
title = "Graded-ring structure on the Rees algebra"
order = 21
lean = ["AlgebraicGeometry.reesGrading.instGradedRing"]
tags = ["latex:proposition"]
uses = ["def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-component-finite-support", "lemma-nagata-rees-components-unique", "lemma-nagata-rees-piece-mul", "lemma-nagata-rees-sum-components"]
+++
The family $n\mapsto\mathcal R_A(I)_n$ defines an
$\mathbb N$-graded-ring structure on $\mathcal R_A(I)$.

## Proof

Use [lemma-nagata-rees-piece-mul] for graded multiplication,
[lemma-nagata-rees-sum-components] for existence of the direct-sum
decomposition, and [lemma-nagata-rees-components-unique] for
uniqueness.
