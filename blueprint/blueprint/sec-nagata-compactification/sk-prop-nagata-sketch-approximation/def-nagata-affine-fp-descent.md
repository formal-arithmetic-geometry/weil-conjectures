+++
id = "def-nagata-affine-fp-descent"
kind = "definition"
title = "Finite-stage model of a finitely presented affine algebra"
order = 351
uses = ["def-nagata-directed-finite-upper-bound", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Suppose $S_{\lambda_0}=\operatorname{Spec}(A_{\lambda_0})$,
$S=\operatorname{Spec}(A)$, and fix a finite presentation

$$
B=A[x_1,\ldots,x_n]/(r_1,\ldots,r_m).
$$

Select finite-stage lifts of every coefficient of every $r_j$, let
$\lambda_B$ be their selected common upper bound, let
$r_{j,\lambda_B}$ be the lifted polynomials, and define

$$
B_{\lambda_B}
=A_{\lambda_B}[x_1,\ldots,x_n]/
(r_{1,\lambda_B},\ldots,r_{m,\lambda_B}).
$$

Define $\beta_B$ to be the comparison from
$B_{\lambda_B}\otimes_{A_{\lambda_B}}A$ to $B$ induced by the presentation.
