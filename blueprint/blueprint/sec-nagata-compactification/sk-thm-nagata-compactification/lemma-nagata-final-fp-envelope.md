+++
id = "lemma-nagata-final-fp-envelope"
kind = "lemma"
title = "Properties of the final finite-presentation envelope"
order = 400
uses = ["def-nagata-final-fp-envelope", "prop-nagata-finite-type-closed-in-fp"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

The map $i_f^{\mathrm{fp}}\colon X\hookrightarrow X_f^{\mathrm{fp}}$ is a
closed immersion over $S$, and
$X_f^{\mathrm{fp}}\to S$ is separated and of finite presentation.

## Proof

These are precisely the three properties established for the constructed
envelope in [prop-nagata-finite-type-closed-in-fp].
