+++
id = "lem-weil-pbc-derived-cohomology-continuity"
kind = "lemma"
title = "Continuity for bounded-below etale complexes"
order = 1238
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-etale-cohomology-continuity", "prop-weil-pbc-inverse-image-exact", "thm-weil-pbc-hypercover-cohomology"]
+++
Let $X=\varprojlim_jX_j$ be a cofiltered system of quasi-compact
quasi-separated schemes [def-weil-pbc-scheme-conventions] with affine
transition maps. For a finite ring $\Lambda$, let $K_i\in\Dplus(X_{i,\Et},
\Lambda)$ and let $K_j,K$ be its inverse images
[def-weil-pbc-inverse-image]. Then the canonical restriction map is an
isomorphism

$$
 \varinjlim_{j\geq i}H^nR\Gamma(X_{j,\Et},K_j)
 \xrightarrow{\sim}H^nR\Gamma(X_{\Et},K)
 \qquad(n\in\mathbb Z).
$$

## Proof

Choose $a$ below the cohomological support of $K_i$, in
[def-weil-pbc-derived-categories]. Exact inverse image in
[prop-weil-pbc-inverse-image-exact] preserves this bound and commutes with
truncations and cohomology sheaves. To calculate degree $n$, one may replace
all these complexes by their truncations in degrees $[a,n]$. Indeed the
complementary truncation starts in degree $n+1$, and its injective resolution
and derived sections have no cohomology in degrees at most $n$.

For a single sheaf in one degree, the assertion is
[lemma-weil-pbc-etale-cohomology-continuity]. Its proof works in
$\Lambda$-module sheaves by the module version of
[thm-weil-pbc-hypercover-cohomology]; its cochains and refinements are
unchanged. Build a bounded truncation by its finite sequence of triangles

$$
 \tau_{\leq b-1}K_i\longrightarrow\tau_{\leq b}K_i
 \longrightarrow\mathcal H^b(K_i)[-b]\longrightarrow .
$$

Apply derived sections at all stages and at the limit. Filtered colimits of
modules are exact, so their long exact cohomology sequences remain exact
after taking the colimit. The five lemma, inductively in $b-a$, proves the
comparison in all degrees for every finite truncation. The preceding
truncation argument then gives the assertion for $K_i$. All arrows used are
the restriction arrows, so this proves the named map, naturally in the
complex and in the inverse system.
