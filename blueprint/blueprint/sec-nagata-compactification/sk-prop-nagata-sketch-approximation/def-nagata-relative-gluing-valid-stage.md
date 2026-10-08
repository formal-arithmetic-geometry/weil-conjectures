+++
id = "def-nagata-relative-gluing-valid-stage"
kind = "definition"
title = "Cocycle-valid stage for the relative datum"
order = 360
uses = ["def-nagata-directed-finite-upper-bound", "def-nagata-morphism-equality-stage", "def-nagata-qc-open-equality-stage", "def-nagata-relative-gluing-datum-descent", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

For the raw datum, form the finite list of required equalities of overlap
opens, inverse identities, and triple-overlap cocycles. Attach to each the
selected equality stage from the preceding constructions and define
$\lambda_{\mathrm{rel}}(X/S)$ to be their common upper bound together with
$\lambda_{\mathrm{raw}}(X/S)$. Let
$\mathsf R_{X,\lambda_{\mathrm{rel}}}$ be the raw datum transported to this
stage.
Canonical comparison maps identify the source and target of each later-stage
equality. Transporting its witness preserves the equation, so the finite
upper-bound list is well typed.
