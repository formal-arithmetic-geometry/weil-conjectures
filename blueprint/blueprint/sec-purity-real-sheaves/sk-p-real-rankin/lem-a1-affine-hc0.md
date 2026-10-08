+++
id = "lem-a1-affine-hc0"
kind = "lemma"
title = "Vanishing of $H_c^0$ on a nonproper curve"
order = 2659
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-pbc-constructible-complexes", "def-wf-weil-category"]
+++
Let $U_0$ be a smooth geometrically connected affine curve and let
$\mathcal F$ be a lisse Weil sheaf
on $U_0$. Then, in the
compactly supported
cohomology of [def-weil-ordinary-compact-cohomology],
$H_c^0(U,\mathcal F)=0$.

## Proof

A class in $H_c^0$ is a global section of $\mathcal F$ whose support
is proper over the base field. By lissity in
[def-weil-pbc-constructible-complexes], a global section of
$\mathcal F$ is locally constant, so on the connected curve it is
determined by its value at one geometric point: a section vanishing at
one point is zero; consequently the support of a nonzero global lisse
section is all of $U$, which is not proper. Hence only the zero
section has compact support, and $H_c^0=0$.
