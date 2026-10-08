+++
id = "lem-pur-projection-purity-agreement"
kind = "lemma"
title = "Agreement with the affine-line route on affine space"
order = 2019
uses = ["cor-pur-affine-space-purity", "def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-frame-class", "def-pur-smooth-purity-map", "def-sbc-smooth-morphisms", "def-weil-scheme-morphism-properties", "lem-pur-dnc-section-geometry", "prop-pur-affine-space-purity-compatibilities", "thm-pur-affine-line-purity", "thm-pur-composition-coherence", "thm-pur-dnc-invariance"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
for the projection $p_d:\mathbf A^d_Y\to Y$ the smooth purity map
$\gamma_{p_d,K}$ of [def-pur-smooth-purity-map] equals the
affinity-space purity comparison of [cor-pur-affine-space-purity],
i.e. the ordered composite of the $d$ affinity-line purity maps of
[thm-pur-affine-line-purity].

## Proof

Both maps are canonical and, by [thm-pur-composition-coherence]
and [prop-pur-affine-space-purity-compatibilities], they are
compatible with the tower of affine projections. It therefore suffices
to compare them after restriction to a geometric fiber of $Y$, where
both are determined by the Kummer computation: the dualizing-object
identification of [def-pur-smooth-purity-map] for $p_d$ comes
from the deformation of the diagonal $\Delta$ and the standard-pair
computation of [lem-pur-dnc-section-geometry](4) – the diagonal
of the standard pair $(\mathbf A^{2d}_Y,\Delta)$ has normal bundle the
trivial rank-$d$ bundle $T_{p_d}$, and the DNC invariance of
[thm-pur-dnc-invariance] is the identity on the standard pair –
whose class, by
[lem-pur-dnc-section-geometry] and the definition of the
[def-pur-frame-class] (class of a frame), is the $d$-fold
exterior product of the rank-one Kummer boundaries, i.e. the
$d$-fold product of the affinity-line orientations; the affinity-space
purity of [cor-pur-affine-space-purity] is built from exactly the
same $d$-fold product of the affinity-line orientations. The two
assemblies differ only by the canonical reassociations of the package
(the Koszul signs are $+1$, since all shift factors are of even
degree, by [prop-pur-affine-space-purity-compatibilities]); hence
the maps agree.
