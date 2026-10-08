+++
id = "lemma-nagata-intermediate-specialization-boundary"
kind = "lemma"
title = "A specialization leaving $U_i$ meets the forbidden boundary"
order = 288
lean = ["AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph"]
uses = ["def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-boundary-loci", "lemma-nagata-proper-extension-graph-closed"]
+++
Let a point in the image of $U_i$ specialize in $U\times_SX_i$ to a point
$(u,x)$. There is a point $v\in V_i$ with
$\psi_i(v)=u$ and image $x$ in $X_i$. If $u\notin U_i$, then
$v\in Z_{i,j}$ and $x\in\overline Z_{i,j}$.

## Proof

The image of $U_i$ is contained in the image of
$\gamma_i\colon V_i\to U\times_SX_i$. The latter image is closed by
[lemma-nagata-proper-extension-graph-closed]; hence the specialization
$(u,x)$ is $\gamma_i(v)$ for some $v\in V_i$. Thus
$\psi_i(v)=u$ and the image of $v$ in $X_i$ is $x$. If $u\notin U_i$, then
$u\in Z_j$, so $v\in Z_{i,j}=\psi_i^{-1}(Z_j)$. Therefore
$x\in Z_{i,j}\subseteq\overline Z_{i,j}$.
