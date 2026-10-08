+++
id = "lemma-nagata-final-noetherian-compactification"
kind = "lemma"
title = "Property of the selected Noetherian compactification"
order = 376
uses = ["def-nagata-final-noetherian-compactification", "lemma-nagata-final-descended-model", "thm-nagata-noetherian"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

The constructed $C_{Y,\lambda_Y}$ is a compactification of
$Y_{\lambda_Y}\to S_{\lambda_Y}$.

## Proof

The base is Noetherian and the descended morphism is separated and of
finite presentation, hence of finite type. Therefore
[thm-nagata-noetherian] applies to the
explicitly selected recursive construction and gives the assertion.
