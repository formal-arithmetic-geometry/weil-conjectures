+++
id = "def-nagata-finite-presentation-descent"
kind = "definition"
title = "Finite-presentation descent construction"
order = 362
uses = ["def-nagata-relative-gluing-valid-stage"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Define

$$
X^{\mathrm{desc}}_{\lambda_{\mathrm{rel}}}
$$

by gluing the valid relative datum
$\mathsf R_{X,\lambda_{\mathrm{rel}}}$. Define

$$
\epsilon_X\colon
X^{\mathrm{desc}}_{\lambda_{\mathrm{rel}}}
\times_{S_{\lambda_{\mathrm{rel}}}}S
\longrightarrow X
$$

by gluing the chartwise base-change identifications.
The relative gluing axioms instantiate the scheme-gluing construction. Base
change preserves the affine charts and overlap maps, so the base-changed
object is canonically the gluing of the base-changed datum; chartwise
comparisons glue to $\epsilon_X$.
