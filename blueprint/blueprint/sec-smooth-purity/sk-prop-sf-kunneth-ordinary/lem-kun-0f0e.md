+++
id = "lem-kun-0f0e"
kind = "lemma"
title = "Tensor with a constant complex over $\\mathbf Z$"
order = 1737
uses = ["def-kun-constant-sheaf", "def-kun-derived-tensor", "def-kun-truncations", "def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions"]
+++
Let $X$ be a
quasi-compact and
quasi-separated scheme. For $E\in\Dplus(X_{\Et})$ and
$K\in\Dplus(\mathbf Z)$, the canonical map

$$
\RGamma(X_{\Et},E)\kunotimes{\mathbf Z}K\longrightarrow
\RGamma\bigl(X_{\Et},E\kunotimes{\mathbf Z}\underline{K}\bigr)
$$

is an isomorphism.

## Proof

Both sides are triangulated functors in $K\in\Dplus(\mathbf Z)$
([def-kun-derived-tensor], [def-weil-pbc-etale-cohomology]),
and for $K=\mathbf Z$ placed in degree zero the map is the unit
constraint of the tensor product, hence an isomorphism; the same holds
for every bounded complex of free $\mathbf Z$-modules, both sides
being compatible with finite direct sums and shifts on the nose.
For a general bounded-below $K$ write $K=\varinjlim_N\sigma_{\ge -N}K$ as the filtered colimit of its stupid truncations
([def-kun-truncations]); since $E$ is bounded below, in each
cohomological degree the tensor product
$\RGamma(X_{\Et},E)\otimes_{\mathbf Z}K$ involves only finitely many
degrees of $K$ below any bound, so the horizontal maps are the
colimits of the isomorphisms for the truncations, and likewise for
$\RGamma(X_{\Et},E\otimes_{\mathbf Z}\underline{K})$ because
$\underline{K}$ is the colimit of the $\underline{\sigma_{\ge -N}K}$
([def-kun-constant-sheaf]) and cohomology commutes with filtered
colimits of complexes. Hence the map is an isomorphism for every
$K\in\Dplus(\mathbf Z)$.
