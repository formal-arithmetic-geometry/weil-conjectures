+++
id = "lemma-nagata-final-ambient-proper"
kind = "lemma"
title = "The final ambient morphism is proper"
order = 404
uses = ["def-nagata-final-compactification", "lemma-nagata-final-basechanged-compactification", "lemma-nagata-final-compactification-spec", "prop-nagata-closed-subscheme-compactifiable"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

The constructed morphism $p_f\colon\overline X_f\to S$ is proper.

## Proof

The ambient scheme $\overline X_f$ is closed in the proper ambient scheme
of $C_f^{\mathrm{fp}}$. A closed immersion followed by a proper morphism is
proper; this is the properness part of the closed-subscheme construction.
