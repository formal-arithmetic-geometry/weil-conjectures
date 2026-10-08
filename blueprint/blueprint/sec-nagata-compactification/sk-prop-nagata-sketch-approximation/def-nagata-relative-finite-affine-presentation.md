+++
id = "def-nagata-relative-finite-affine-presentation"
kind = "definition"
title = "Selected finite relative affine presentation"
order = 357
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $S$ be qcqs and let $X\to S$ be of finite presentation. Select a
finite affine cover of
$S$, finite affine covers of its inverse images in $X$, finite
presentations of all chart algebras over the base chart algebras, finite
basic-open presentations of the overlaps, and the two directions of every
overlap isomorphism. Record these data and their finite identity, inverse,
and cocycle equations as $\mathsf R_X$.
Quasi-compactness gives finite affine covers and quasi-separatedness makes
overlaps quasi-compact. Finite presentation supplies finite generators and
relations; record both overlap directions and the finite identity and
cocycle equations as $\mathsf R_X$.
