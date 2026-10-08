+++
id = "def-nagata-final-noetherian-compactification"
kind = "definition"
title = "Noetherian compactification used in the final assembly"
order = 375
uses = ["def-nagata-final-descended-model", "def-nagata-noetherian-compactification", "lemma-nagata-final-descended-model"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

For $Y\to S$ as in [def-nagata-final-descended-model], define

$$
C_{Y,\lambda_Y}
=\mathsf C_{\mathrm{Noeth}}
(Y_{\lambda_Y}/S_{\lambda_Y}).
$$
