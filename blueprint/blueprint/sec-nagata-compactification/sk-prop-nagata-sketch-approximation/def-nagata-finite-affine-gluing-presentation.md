+++
id = "def-nagata-finite-affine-gluing-presentation"
kind = "definition"
title = "Selected finite affine gluing presentation"
order = 332
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $S$ be quasi-compact and quasi-separated. Select a finite affine cover
$S=\bigcup_{a=1}^nU_a$. For every pair $(a,b)$, select a finite affine
cover $(U_{ab,r})_r$ of $U_a\cap U_b$ and then finite basic-open covers of
each $U_{ab,r}$ as an open of $U_a$ and of $U_b$. Record the resulting
chart rings, inverted elements, two directions of each overlap map, and the
finite lists of identity, inverse, and triple-cocycle equalities. Call this
finite record $\mathsf G_S$.
