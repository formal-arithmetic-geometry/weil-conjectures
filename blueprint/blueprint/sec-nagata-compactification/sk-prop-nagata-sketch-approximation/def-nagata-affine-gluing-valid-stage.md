+++
id = "def-nagata-affine-gluing-valid-stage"
kind = "definition"
title = "Cocycle-valid stage of an affine gluing presentation"
order = 336
uses = ["def-nagata-affine-gluing-coefficient-stage", "def-nagata-directed-finite-upper-bound", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

For every identity, inverse, open-preservation, and triple-cocycle equation
in $\mathsf G_S$, select a finite stage at which that equation holds on the
chosen generators after localization. Define
$\lambda_{\mathrm{glue}}(S)$ to be the selected upper bound of
$\lambda_{\mathrm{coeff}}(S)$ and these finitely many witness stages. Let
$\mathsf G_{S,\lambda_{\mathrm{glue}}}$ be the pullback of the raw datum to
this stage.
