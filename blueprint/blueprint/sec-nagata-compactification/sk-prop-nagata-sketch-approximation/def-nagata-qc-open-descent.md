+++
id = "def-nagata-qc-open-descent"
kind = "definition"
title = "Finite-stage model of a quasi-compact open"
order = 347
uses = ["def-nagata-basechanged-system", "def-nagata-directed-finite-upper-bound", "lemma-nagata-filtered-colimit-finite-data"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Fix $\lambda_0$, assume $Y_{\lambda_0}$ is qcqs, and put
$Y=S\times_{S_{\lambda_0}}Y_{\lambda_0}$, and let $W\subseteq Y$ be a
quasi-compact open. Select finitely many affine opens of
$Y_{\lambda_0}$ meeting the image of $W$. On their inverse limits, write
$W$ as a finite union of basic opens $D(f_{ak})$. Choose finite-stage
lifts $f_{ak,\lambda_{ak}}$ and define

$$
\lambda_W=u(\{\lambda_0\}\cup\{\lambda_{ak}\}_{a,k}),
\qquad
W_{\lambda_W}=\bigcup_{a,k}D(f_{ak,\lambda_W})
\subseteq Y_{\lambda_W}.
$$

Quasi-compactness supplies a finite affine cover; on each chart the inverse
limit identifies the coordinate ring with the filtered colimit, so the open
has a finite basic-open presentation. Record those functions and lifts in
the witness before taking the common upper bound.
