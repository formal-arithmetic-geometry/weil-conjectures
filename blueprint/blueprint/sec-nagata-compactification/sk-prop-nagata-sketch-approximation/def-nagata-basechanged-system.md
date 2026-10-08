+++
id = "def-nagata-basechanged-system"
kind = "definition"
title = "Base-changed system over a chosen stage"
order = 346
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Fix $\lambda_0\in I$ and a scheme $Y_{\lambda_0}$ equipped with a morphism
to $S_{\lambda_0}$. On the cofinal directed subsystem
$I_{\lambda_0}=\{\lambda\mid\lambda_0\leq\lambda\}$, define

$$
Y_\lambda=Y_{\lambda_0}\times_{S_{\lambda_0}}S_\lambda,
\qquad
Y=Y_{\lambda_0}\times_{S_{\lambda_0}}S.
$$

The transition morphisms $Y_\mu\to Y_\lambda$ for
$\lambda\leq\mu$ are the canonical base changes of the inverse-system
transitions $S_\mu\to S_\lambda$, and the maps $Y\to Y_\lambda$ are the
projections induced by $S\to S_\lambda$.
