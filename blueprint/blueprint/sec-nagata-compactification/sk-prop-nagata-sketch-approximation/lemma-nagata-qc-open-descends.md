+++
id = "lemma-nagata-qc-open-descends"
kind = "lemma"
title = "Property of the descended quasi-compact open"
order = 348
uses = ["def-nagata-qc-open-descent", "lemma-nagata-directed-finite-upper-bound"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

The constructed $W_{\lambda_W}$ is quasi-compact, and its inverse image in
$Y$ is exactly $W$.

## Proof

A finite union of basic opens is quasi-compact. Every lifted defining
function has reached the common stage $\lambda_W$, and base change sends
$D(f_{ak,\lambda_W})$ to $D(f_{ak})$. Taking the finite union therefore
recovers precisely the selected basic-open presentation of $W$.
