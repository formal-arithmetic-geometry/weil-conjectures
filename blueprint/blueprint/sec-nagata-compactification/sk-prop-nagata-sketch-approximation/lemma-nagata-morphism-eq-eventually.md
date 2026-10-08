+++
id = "lemma-nagata-morphism-eq-eventually"
kind = "lemma"
title = "Eventual equality of morphisms, [stacks-project]"
order = 356
uses = ["def-nagata-morphism-equality-stage", "lemma-nagata-directed-finite-upper-bound", "lemma-nagata-qc-open-eq-eventually"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

For every $\lambda\geq\lambda_{\varphi=\psi}$, the base changes of
$\varphi_{\lambda_0}$ and $\psi_{\lambda_0}$ to $S_\lambda$ are equal.

## Proof

Above the selected stage, the two maps have equal inverse images of every
target chart. On a finite affine cover of each common inverse image, their
ring maps agree on a finite generating set and hence agree. The local
equalities glue to the asserted global equality and persist at later stages.
