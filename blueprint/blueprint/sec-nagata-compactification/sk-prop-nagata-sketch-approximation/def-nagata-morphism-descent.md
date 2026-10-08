+++
id = "def-nagata-morphism-descent"
kind = "definition"
title = "Finite-stage model of a morphism"
order = 353
uses = ["def-nagata-affine-fp-descent", "def-nagata-directed-finite-upper-bound", "def-nagata-qc-open-descent", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $X_{\lambda_0},Y_{\lambda_0}$ be of finite presentation over
$S_{\lambda_0}$, write
$X_{\lambda_0,S}=X_{\lambda_0}\times_{S_{\lambda_0}}S$ and
$Y_{\lambda_0,S}=Y_{\lambda_0}\times_{S_{\lambda_0}}S$, and let
$\varphi\colon X_{\lambda_0,S}\to Y_{\lambda_0,S}$ be an $S$-morphism.
Choose a finite affine target cover, descend its quasi-compact inverse-image
opens, choose finite affine covers of those opens, and descend each affine
ring map using its finite generator-and-relation data. Include the finitely
many pairwise-overlap equality stages in one selected upper bound
$\lambda_\varphi$, and define

$$
\varphi_{\lambda_\varphi}\colon
X_{\lambda_\varphi}\longrightarrow Y_{\lambda_\varphi}
$$

by gluing the descended affine maps.
Retain comparison isomorphisms for each descended open, transport every
affine map through them, and include the finitely many overlap equalities in
the common upper bound; the transported maps glue at the selected stage.
