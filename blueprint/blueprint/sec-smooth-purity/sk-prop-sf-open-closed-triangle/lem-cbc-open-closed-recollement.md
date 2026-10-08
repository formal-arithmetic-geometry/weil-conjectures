+++
id = "lem-cbc-open-closed-recollement"
kind = "lemma"
title = "Open-closed recollement"
order = 1850
uses = ["def-weil-open-closed-recollement", "def-weil-pbc-derived-categories", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-finite-direct-image-exact", "prop-weil-open-closed-recollement-adjunctions"]
+++
Let $i:Z\hookrightarrow X$ be a
closed immersion with
complementary
open immersion
$j:U\hookrightarrow X$, and let $\Lambda$ be a finite commutative
ring. For every $K\in D^+(X_{\Et},\Lambda)$ there is a functorial
distinguished triangle

$$
j_!j^{-1}K\longrightarrow K\longrightarrow i_*i^{-1}K
\longrightarrow j_!j^{-1}K[1],
$$

where $i_*$ is the (exact) direct image of the closed immersion, and
the triangle is compatible with the adjunctions
$j_!\dashv j^{-1}$, $i^{-1}\dashv i_*$ of
[prop-weil-open-closed-recollement-adjunctions].

## Proof

The closed immersion $i$ is finite,
so $i_*$ is exact by [lemma-weil-pbc-finite-direct-image-exact].
A short exact sequence of sheaves
$0\to j_!j^{-1}F\to F\to i_*i^{-1}F\to0$ is obtained from the
stalkwise description of [def-weil-pbc-extension-by-zero]: on $U$
the first map is the counit of $j_!\dashv j^{-1}$, an isomorphism
by the identity $j^*j_!\cong\operatorname{id}$ of
[prop-weil-open-closed-recollement-adjunctions], and the third map is
$0$ there; on $Z$ the first term already has stalk $0$, the
spaces of the first two terms at a point of $Z$ agree, and the
third map is the (inverse-image) unit of
[prop-weil-open-closed-recollement-adjunctions], an isomorphism.
The exact
kernel–cokernel description at every stalk gives the short exact
sequence, and taking the associated distinguished triangle in the
derived category gives the assertion; functoriality and the
adjunction compatibilities are those of the short exact sequence and
of [def-weil-open-closed-recollement].
