+++
id = "def-nagata-affine-neighbourhood-generic-points"
kind = "definition"
title = "Affine neighbourhood containing selected generic points"
order = 314
uses = ["lemma-nagata-affine-neighbourhood-generic-points-exists"]
+++
**Status.** Bypassed by the formalized route: the affine cover meeting the
selected generic points is produced in one step by
`AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter`
and `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter`.

Let $X$ be quasi-separated, let $x\in X$, and let
$\eta_1,\ldots,\eta_r$ be generic points of distinct irreducible
components. Choose one witness from
[lemma-nagata-affine-neighbourhood-generic-points-exists] and denote
its affine open by $A(x;\eta_1,\ldots,\eta_r)$.
