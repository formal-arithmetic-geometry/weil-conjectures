+++
id = "lemma-nagata-rees-sum-components"
kind = "lemma"
title = "Reconstruction from homogeneous components"
order = 19
lean = ["AlgebraicGeometry.reesGrading_isInternal"]
uses = ["def-nagata-rees-algebra", "def-nagata-rees-piece", "lemma-nagata-rees-component-finite-support", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul"]
+++
Every $F\in\mathcal R_A(I)$ is the finite sum of the monomials
$F_nt^n$ regarded as elements of $\mathcal R_A(I)_n$.

## Proof

Sum over the finite polynomial support. Equality follows by comparing the
coefficient in every degree.
