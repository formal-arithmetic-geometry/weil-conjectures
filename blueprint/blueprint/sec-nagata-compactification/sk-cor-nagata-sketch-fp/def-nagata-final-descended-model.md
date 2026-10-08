+++
id = "def-nagata-final-descended-model"
kind = "definition"
title = "Separated descended model used in the final assembly"
order = 373
uses = ["def-nagata-final-noetherian-base-system", "def-nagata-separated-descent-stage", "lemma-nagata-final-noetherian-base-system"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

Let $S$ be quasi-compact and quasi-separated and let $Y\to S$ be
separated and of finite presentation.
Apply the separated-descent construction to
$Y\to S$ relative to $\mathsf N_f=\mathsf N(S)$. Define

$$
\lambda_Y=\lambda_{\mathrm{sep}}(Y/S),
\qquad
Y_{\lambda_Y}
=Y^{\mathrm{sep}}_{\lambda_Y},
$$

and let

$$
\epsilon_Y\colon
Y_{\lambda_Y}
\times_{S_{\lambda_Y}}S
\longrightarrow Y
$$

be the constructed base-change comparison.
