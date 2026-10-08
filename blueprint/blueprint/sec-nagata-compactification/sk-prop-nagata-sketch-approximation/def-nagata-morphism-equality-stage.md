+++
id = "def-nagata-morphism-equality-stage"
kind = "definition"
title = "Stage of equality for two descended morphisms"
order = 355
uses = ["def-nagata-directed-finite-upper-bound", "def-nagata-qc-open-equality-stage", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $\varphi_{\lambda_0},\psi_{\lambda_0}\colon X_{\lambda_0}\to Y_{\lambda_0}$ have equal base change to $S$. On a
finite affine target cover, include the stages at which their inverse-image
opens agree and the stages at which the induced ring maps agree on finite
generator lists. Define $\lambda_{\varphi=\psi}$ to be the selected upper
bound of this finite set.
