+++
id = "lemma-nagata-affine-fp-descends"
kind = "lemma"
title = "Property of affine finite-presentation descent"
order = 352
uses = ["def-nagata-affine-fp-descent"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

The algebra $B_{\lambda_B}$ is finitely presented over
$A_{\lambda_B}$, and the constructed map $\beta_B$ is an isomorphism.

## Proof

The displayed quotient is a finite presentation by construction. Tensoring
it with $A$ sends every lifted relation to the original $r_j$ and preserves
the finite polynomial presentation. Thus the base-changed presentation is
the chosen presentation of $B$, with $\beta_B$ and its generatorwise inverse
mutually inverse.
