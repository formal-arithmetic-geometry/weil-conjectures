+++
id = "lemma-nagata-one-valuation-avoids-boundary"
kind = "lemma"
title = "One valuation extension avoids the forbidden boundary"
order = 294
lean = ["AlgebraicGeometry.TwoOpenSide.KeyDisjoint.avoids"]
uses = ["def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-comparison-space", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-valuation-factor-closed", "lemma-nagata-valuation-open-closed-point", "lemma-nagata-valuation-pair-factors-comparison"]
+++
Let $A$ be a valuation ring with fraction field $K$. Let
$\operatorname{Spec}(K)\to U_1\cap U_2$ be an $S$-morphism and let
$g_i\colon\operatorname{Spec}(A)\to X_i$ be extensions. At least one
$g_i$ factors through $X_i\setminus\overline Z_{i,j}$, and hence determines
a map $\operatorname{Spec}(A)\to W_i$ extending the given generic map.

## Proof

Otherwise the closed point would map into $\overline Z_{1,2}$ under $g_1$
and into $\overline Z_{2,1}$ under $g_2$. By
[lemma-nagata-valuation-pair-factors-comparison], the pair factors
through $X_{12}$, and its closed point then lies in
$X_{12}\cap(\overline Z_{1,2}\times_S\overline Z_{2,1})$, contradicting
part (4) of [lemma-nagata-key-boundary-disjointness]. If the closed point avoids
one of the two boundaries, its inverse image of the corresponding open
complement is an open subset of $\operatorname{Spec}(A)$ containing the
closed point. By
[lemma-nagata-valuation-open-closed-point] this open is all of
$\operatorname{Spec}(A)$. The associated $g_i$ therefore factors
through $X_i\setminus\overline Z_{i,j}$, and the open immersion
$X_i\setminus\overline Z_{i,j}\hookrightarrow W_i$ supplies the asserted
extension.
