+++
id = "lemma-nagata-morphism-descends"
kind = "lemma"
title = "Property of the descended morphism, [stacks-project]"
order = 354
uses = ["def-nagata-morphism-descent", "lemma-nagata-affine-fp-descends", "lemma-nagata-qc-open-descends"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

The base change of the constructed
$\varphi_{\lambda_\varphi}$ to $S$ is $\varphi$.

## Proof

The inverse-image opens pull back to the original opens by the quasi-compact
open descent property. On each affine piece, the descended ring map pulls
back to the original map by the affine finite-presentation property. The
selected equality stages make those local maps agree on all overlaps, so
their gluing pulls back to the gluing of the original local maps, namely
$\varphi$.
