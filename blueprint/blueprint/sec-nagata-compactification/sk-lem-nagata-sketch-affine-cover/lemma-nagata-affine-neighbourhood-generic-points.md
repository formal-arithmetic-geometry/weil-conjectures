+++
id = "lemma-nagata-affine-neighbourhood-generic-points"
kind = "lemma"
title = "Property of the selected affine neighbourhood, [stacks-project]"
order = 315
uses = ["def-nagata-affine-neighbourhood-generic-points", "lemma-nagata-affine-neighbourhood-generic-points-exists"]
+++
**Status.** Bypassed by the formalized route: the affine cover meeting the
selected generic points is produced in one step by
`AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter`
and `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter`.

The constructed open $A(x;\eta_1,\ldots,\eta_r)$ is affine and contains
$x$ and every $\eta_i$.

## Proof

The selected witness exists by
[lemma-nagata-affine-neighbourhood-generic-points-exists]; its
specification says that the open is affine and contains $x$ and every
selected generic point.
