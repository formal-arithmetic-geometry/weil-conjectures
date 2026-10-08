+++
id = "lemma-nagata-qc-open-eq-eventually"
kind = "lemma"
title = "Eventual equality of descended quasi-compact opens"
order = 350
uses = ["def-nagata-qc-open-equality-stage"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

For every $\lambda\geq\lambda_{W_1=W_2}$, the inverse images of
$W_{1,\lambda_0}$ and $W_{2,\lambda_0}$ in $Y_\lambda$ are equal.

## Proof

Equality of finite unions of basic opens is equivalent, chartwise, to the
two finite lists of radical containments. Each chosen power identity holds
at its witness stage and at every later stage. Their common upper bound
therefore imposes both inclusions on every affine chart, hence equality of
the global opens.
