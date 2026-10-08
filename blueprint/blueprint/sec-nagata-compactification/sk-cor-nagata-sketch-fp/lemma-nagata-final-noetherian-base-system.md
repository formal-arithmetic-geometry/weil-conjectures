+++
id = "lemma-nagata-final-noetherian-base-system"
kind = "lemma"
title = "Properties of the final Noetherian base system"
order = 372
uses = ["def-nagata-final-noetherian-base-system", "prop-nagata-noetherian-inverse-system"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

In the system of
[def-nagata-final-noetherian-base-system], every $S_\lambda$ is
Noetherian and of finite type over $\mathbf Z$, every transition map is
affine, and $\kappa_S$ is an isomorphism.

## Proof

Apply [prop-nagata-noetherian-inverse-system] to the explicitly
selected system $\mathsf N(S)$.
