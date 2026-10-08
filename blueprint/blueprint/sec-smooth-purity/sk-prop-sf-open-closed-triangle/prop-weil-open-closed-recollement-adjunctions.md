+++
id = "prop-weil-open-closed-recollement-adjunctions"
kind = "theorem"
title = "Adjunctions of the open-closed recollement"
order = 1849
uses = ["def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-extension-by-zero", "def-weil-open-closed-recollement", "def-weil-pbc-proetale-operations", "def-weil-scheme-morphism-properties", "lem-exc-proetale-closed-fully-faithful", "lem-exc-proetale-open-unit", "lem-weil-extension-by-zero-adjunction", "lem-weil-extension-by-zero-exact", "prop-weil-pbc-kinjective-resolutions-exist", "prop-weil-pbc-proetale-constant-exact"]
tags = ["latex:proposition"]
+++
For complementary open and closed immersions $j:U\hookrightarrow X$,
$i:Z\hookrightarrow X$ as in the open-closed recollement, one has
$j_!\dashv j^*$ and $i^*\dashv Ri_*$ on the ambient ordinary derived
categories with finite constant coefficients. The open unit and the closed
counit are isomorphisms
$$
 \operatorname{id}\xrightarrow{\sim}j^*j_!,\qquad
 i^*Ri_*\xrightarrow{\sim}\operatorname{id}.
$$
The operations are those of extension by zero, derived direct image, and
derived pullback, tensor and hom.

## Proof

The open adjunction is the extension-by-zero adjunction. Both functors are
exact, so they pass to ordinary derived categories with the same adjunction
and triangle identities. The unit is an isomorphism term by term by
[lem-exc-proetale-open-unit].

For the closed adjunction, choose a K-injective resolution $M\to J$ on $Z$.
Since $i^*$ is exact, $i_*J$ is K-injective: its Hom complex from an acyclic
complex $N$ is the Hom complex from the acyclic $i^*N$ to $J$, hence
acyclic. Thus $i_*J$ represents $Ri_*M$, and complex-level adjunction gives
$i^*\dashv Ri_*$. Exactness of $i^*$ lets us compute the derived counit by
$i^*i_*J\to J$. This is an isomorphism in every degree by
[lem-exc-proetale-closed-fully-faithful]. Hence the derived counit is an
isomorphism. This calculation does not assume exactness of $i_*$ for an
arbitrary closed immersion; the complement's quasi-compactness is needed for
the separate sheaf-exactness and recollement theorems above.
