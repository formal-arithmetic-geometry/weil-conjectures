+++
id = "def-nagata-noetherian-stage"
kind = "definition"
title = "Finite-type Noetherian stage"
order = 338
uses = ["def-nagata-affine-gluing-valid-stage"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Define $S_{\lambda_{\mathrm{glue}}}$ to be the scheme obtained by gluing
$\mathsf G_{S,\lambda_{\mathrm{glue}}}$. More generally, for every finite
refinement $\lambda$ of the coefficient system satisfying the same finite
equations, define $S_\lambda$ by gluing the corresponding datum.
