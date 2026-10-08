+++
id = "lem-kun-derived-tensor-triangulated"
kind = "lemma"
title = "The derived tensor product is triangulated in each variable"
order = 1685
uses = ["def-kun-derived-tensor", "def-weil-pbc-derived-categories", "lem-kun-derived-tensor-well-defined"]
+++
Let $\Lambda$ be a commutative ring and $T$ a scheme. For every
$K_2\in D(T_{\Et},\Lambda)$ the functor
$K\mapsto K\kunotimes{\Lambda}K_2$ of [def-kun-derived-tensor]
is an exact functor of triangulated categories, and likewise in the
second variable.

## Proof

Fix $K_2$ and choose a K-flat model $P\to K_1$ of $K_1$, so that
$K_1\kunotimes{\Lambda}K_2=P\otimes_\Lambda K_2$ by
[def-kun-derived-tensor]. The functor
$P\otimes_\Lambda-$ is additive, preserves shifts and carries
distinguished triangles of complexes to distinguished triangles,
because the total complex of the tensor product with a complex of flat
sheaves is exact degreewise; the resulting maps do not depend on the
chosen K-flat model of $K_1$ by
[lem-kun-derived-tensor-well-defined]. The same argument applies
in the second variable.
