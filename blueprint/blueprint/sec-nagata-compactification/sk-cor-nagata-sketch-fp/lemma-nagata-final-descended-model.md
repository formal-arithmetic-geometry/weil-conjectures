+++
id = "lemma-nagata-final-descended-model"
kind = "lemma"
title = "Properties of the final descended model"
order = 374
uses = ["def-nagata-final-descended-model", "lemma-nagata-final-noetherian-base-system", "lemma-nagata-separated-eventually"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

For $Y\to S$ as in [def-nagata-final-descended-model], the morphism
$Y_{\lambda_Y}\to S_{\lambda_Y}$ is separated and of
finite presentation, $S_{\lambda_Y}$ is Noetherian, and $\epsilon_Y$ is an
isomorphism over $S$.

## Proof

The first and third assertions are the property of the constructed separated
descent stage. The selected base stage belongs to $\mathsf N_f$, so it is
Noetherian by [lemma-nagata-final-noetherian-base-system].
