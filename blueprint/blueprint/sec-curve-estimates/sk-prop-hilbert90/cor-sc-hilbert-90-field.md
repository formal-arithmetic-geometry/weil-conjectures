+++
id = "cor-sc-hilbert-90-field"
kind = "theorem"
title = "Hilbert 90 for a field"
order = 883
uses = ["thm-sc-hilbert-90"]
lean = ["AlgebraicGeometry.Scheme.subsingleton_cohomologicalPicardGroup_of_field"]
+++
Let $K$ be a field. Then $H^1(\operatorname{Spec}K_{\Et},\mathbf G_m)=0$
(and also $H^1((\operatorname{Spec}K)_{\mathrm{Zar}},\mathcal O^{\times})=0$).

## Proof

By [thm-sc-hilbert-90] with $X=\operatorname{Spec}K$, both groups are
isomorphic to the group of isomorphism classes of invertible
$\mathcal O_X$-modules. The underlying space of $X$ is a point, so a
quasi-coherent $\mathcal O_X$-module is a $K$-vector space and an
invertible one is a one-dimensional $K$-vector space, i.e. isomorphic
to $K=\mathcal O_X$. Hence the group is trivial.
