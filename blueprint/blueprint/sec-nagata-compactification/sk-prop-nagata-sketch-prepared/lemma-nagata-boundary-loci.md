+++
id = "lemma-nagata-boundary-loci"
kind = "lemma"
title = "Closedness and disjointness of the four boundary loci"
order = 267
lean = ["AlgebraicGeometry.TwoOpenSide.closure_image_preimage_inter"]
uses = ["def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "lemma-nagata-graph-extension"]
+++
The subschemes $Z_i$ are closed in $U$. Each $Z_{i,k}$ is closed in
$V_i$, their underlying closed sets are disjoint, and $\psi_i$ is an
isomorphism over an open neighbourhood of $Z_i$.

## Proof

Since the support of $Z_i$ is $U\setminus U_j$, it is closed in $U$ and
contained in $U_i$. Base change of this closed immersion along $\psi_i$
gives each closed immersion $Z_{i,k}\hookrightarrow V_i$. The supports of
$Z_i$ and $Z_j$ are disjoint because
$(U\setminus U_j)\cap(U\setminus U_i)=U\setminus(U_i\cup U_j)=\varnothing$;
their inverse images in $V_i$ are consequently disjoint. Finally,
$Z_i\subseteq U_i$, and [lemma-nagata-graph-extension] identifies
$\psi_i^{-1}(U_i)\to U_i$ with an isomorphism. This gives the required
isomorphism on the open neighbourhood $U_i$ of $Z_i$.
