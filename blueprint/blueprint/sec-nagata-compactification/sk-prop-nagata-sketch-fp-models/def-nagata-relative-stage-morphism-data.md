+++
id = "def-nagata-relative-stage-morphism-data"
kind = "definition"
title = "Finite-stage data for a morphism"
order = 380
uses = ["def-nagata-glued-limit-comparison", "def-nagata-noetherian-inverse-system"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $X\to S$ be a morphism and choose the inverse systems
$\mathsf N(X)$ and $\mathsf N(S)$ together with their comparison maps to
$X$ and $S$. A finite-stage datum for this morphism consists of indices
$\lambda_X$ and $\lambda_S$, a morphism
$\varphi_{\lambda_X,\lambda_S}\colon X_{\lambda_X}\to S_{\lambda_S}$,
and an equality after composing with the two limit projections: the map
$X\to S\to S_{\lambda_S}$ equals
$X\to X_{\lambda_X}\to S_{\lambda_S}$. The datum also records the finite
affine charts and generator-and-relation lists used to construct
$\varphi_{\lambda_X,\lambda_S}$. Finally it records a finite affine cover
of $X$, compatible opens in
$X_{\lambda_X}\times_{S_{\lambda_S}}S$, and chartwise surjections of
coordinate rings showing that the induced comparison
$X\to X_{\lambda_X}\times_{S_{\lambda_S}}S$ is an immersion; all overlap
equalities are included in the datum.
