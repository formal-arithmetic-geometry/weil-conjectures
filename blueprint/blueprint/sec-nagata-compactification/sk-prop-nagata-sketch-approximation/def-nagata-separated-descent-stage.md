+++
id = "def-nagata-separated-descent-stage"
kind = "definition"
title = "Separated stage of a descended finite-presentation model"
order = 368
uses = ["def-nagata-finite-presentation-descent", "lemma-nagata-separated-descent-stage-exists"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $X\to S$ be separated and of finite presentation, and start from its
constructed finite-stage model
$X^{\mathrm{desc}}_{\lambda_{\mathrm{rel}}}\to S_{\lambda_{\mathrm{rel}}}$. Choose one witness from
[lemma-nagata-separated-descent-stage-exists] and define
$\lambda_{\mathrm{sep}}(X/S)$ and
$X^{\mathrm{sep}}_{\lambda_{\mathrm{sep}}(X/S)}$ to be the index and model
recorded by that witness. The eventual separatedness and comparison
properties are stated separately below.
