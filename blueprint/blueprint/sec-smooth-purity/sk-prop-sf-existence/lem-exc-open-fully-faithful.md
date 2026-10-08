+++
id = "lem-exc-open-fully-faithful"
kind = "lemma"
title = "An open immersion is fully faithful on the derived categories"
order = 1809
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "lem-weil-extension-by-zero-exact", "prop-weil-pbc-kinjective-resolutions-exist"]
+++
For an open immersion $g:V\hookrightarrow T$, the derived functors satisfy

$$
Lg^*Rg_*\cong\operatorname{id},
\qquad\text{and}\qquad
Lg^*i_*=0
$$

for the closed complement $i:Z\hookrightarrow T$ of $g$.

## Proof

At the sheaf level $g^*g_*\cong\operatorname{id}$ for an open immersion, by
the description of the inverse and direct images in
[def-weil-pbc-inverse-image], [def-weil-pbc-direct-image]. Extension by
zero along $g$ is exact by [lem-weil-extension-by-zero-exact], so
its right adjoint $g^*$ carries K-injective complexes to K-injective
complexes; resolving by
[prop-weil-pbc-kinjective-resolutions-exist] therefore computes
$Lg^*Rg_*$ by the sheaf-level composite, which is the identity. The
second assertion is the sheaf-level vanishing $g^*i_*=0$, the images of
$g$ and $i$ being disjoint.
