+++
id = "def-nagata-final-basechanged-compactification"
kind = "definition"
title = "Base-changed compactification of a separated finitely presented morphism"
order = 377
uses = ["def-nagata-compactification-base-change", "def-nagata-final-descended-model", "def-nagata-final-noetherian-compactification", "lemma-nagata-final-descended-model", "lemma-nagata-final-noetherian-compactification"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

For $Y\to S$ as in [def-nagata-final-descended-model],
let $\overline Y_{\lambda_Y}$ be the ambient term of
$C_{Y,\lambda_Y}$ and let
$j_{Y,\lambda_Y}\colon Y_{\lambda_Y} \hookrightarrow\overline Y_{\lambda_Y}$ be its open immersion. Base
change this factorization along $S\to S_{\lambda_Y}$ and set
$\epsilon_Y^{-1}\colon Y\xrightarrow{\sim} Y_{\lambda_Y}\times_{S_{\lambda_Y}}S$. Define the source
map of the resulting factorization to be
$j_{Y,\lambda_Y,S}\circ\epsilon_Y^{-1}$, and define the resulting
factorization to be

$$
\mathsf C^{\mathrm{fp}}(Y/S)
=\bigl(Y\hookrightarrow
\overline Y\longrightarrow S\bigr).
$$
