+++
id = "lemma-nagata-valuation-pair-factors-comparison"
kind = "lemma"
title = "The pair of valuation extensions factors through $X_{12}$"
order = 292
lean = ["AlgebraicGeometry.TwoOpenSide.KeyDisjoint.avoids"]
uses = ["def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-comparison-space", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-valuation-factor-closed"]
+++
Let $A$ be a valuation ring with fraction field $K$. Suppose
$\operatorname{Spec}(K)\to U_1\cap U_2$ is an $S$-morphism and let
$g_i\colon\operatorname{Spec}(A)\to X_i$ be extensions. Then the pair

$$
(g_1,g_2)\colon\operatorname{Spec}(A)\to X_1\times_SX_2
$$

factors through $X_{12}$.

## Proof

The two generic maps have the same image in $U$, so their pair lands in
$V_1\times_UV_2=V_{12}$. Composing with the canonical image-factor map
gives a factorization of the generic pair through $X_{12}$. The map
$A\to K$ is injective because a valuation ring is a domain. Apply
[lemma-nagata-valuation-factor-closed] to the closed immersion
$X_{12}\hookrightarrow X_1\times_SX_2$ and the morphism
$(g_1,g_2)\colon\operatorname{Spec}(A)\to X_1\times_SX_2$. It extends the
generic factorization to all of $\operatorname{Spec}(A)$.
