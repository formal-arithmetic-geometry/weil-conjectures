+++
id = "lemma-nagata-intermediate-overlap-specialization-closed"
kind = "lemma"
title = "Specialization stability inside the boundary complement"
order = 289
lean = ["AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph"]
uses = ["def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-boundary-loci", "lemma-nagata-intermediate-specialization-boundary", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-proper-extension-graph-closed"]
+++
The image of $U_i$ in
$U\times_S(X_i\setminus\overline Z_{i,j})$ is stable under specialization.

## Proof

Let a point of the image specialize to $(u,x)$ in the displayed target. If
$u\notin U_i$, then
[lemma-nagata-intermediate-specialization-boundary] gives
$x\in\overline Z_{i,j}$, contradicting the definition of the target.
Hence $u\in U_i$. By part (1) of
[lemma-nagata-key-boundary-disjointness], the identity
$\psi_i^{-1}(U_i)=U_i$ forces the point $v$ supplied by
[lemma-nagata-intermediate-specialization-boundary] to lie in $U_i$.
The chosen isomorphism $U_i\cong\psi_i^{-1}(U_i)$ then identifies $x$ with
the graph point of $u$, so $(u,x)$ is again in the image of $U_i$.
