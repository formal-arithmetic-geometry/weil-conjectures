+++
id = "def-nagata-qc-open-equality-stage"
kind = "definition"
title = "Stage of equality for descended quasi-compact opens"
order = 349
uses = ["def-nagata-directed-finite-upper-bound", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $W_{1,\lambda_0},W_{2,\lambda_0}\subseteq Y_{\lambda_0}$ be
quasi-compact opens whose inverse images in $Y$ agree. On a finite affine
cover, choose finite basic-open presentations for both. For every required
radical containment select the finite stage containing a witnessing power
and its finitely many coefficients. Define
$\lambda_{W_1=W_2}$ to be the selected upper bound of those witness stages.
