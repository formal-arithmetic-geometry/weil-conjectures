+++
id = "def-nagata-glued-limit-comparison"
kind = "definition"
title = "Comparison from the original scheme to the inverse limit"
order = 342
uses = ["def-nagata-noetherian-inverse-system"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

The inclusions of every finite coefficient algebra into the original chart
algebra give compatible maps $S\to S_\lambda$. Define

$$
\kappa_S\colon S\longrightarrow\varprojlim_{\lambda\in I_S}S_\lambda
$$

by the universal property of the inverse limit.
