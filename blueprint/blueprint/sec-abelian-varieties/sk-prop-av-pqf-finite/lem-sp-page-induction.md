+++
id = "lem-sp-page-induction"
kind = "lemma"
title = "Page induction"
order = 512
uses = ["def-sp-convergence", "def-sp-spectral-sequence"]
+++
Let $\varphi:E\to E'$ be a morphism of spectral sequences
[def-sp-spectral-sequence]. If $\varphi$ is an isomorphism on the
$E_2$-page in every bidegree, then it is an isomorphism on all pages $E_r$,
$2\leq r\leq\infty$.

## Proof

Each $E_{r+1}$ is the homology of the page $E_r$
([def-sp-spectral-sequence]); a morphism of complexes which is a
quasi-isomorphism induces a homology isomorphism, and the page
identifications are compatible with the morphism. Hence the
$E_2$-isomorphism gives the $E_3$-isomorphism, induction gives all $E_r$, and
the intersection and union formulas in [def-sp-convergence] give
$E_\infty\cong E'_\infty$.
