+++
id = "lemma-nagata-final-open-immersion"
kind = "lemma"
title = "The final source map is a quasi-compact open immersion"
order = 405
uses = ["def-nagata-final-compactification", "lemma-nagata-final-basechanged-compactification", "lemma-nagata-final-compactification-spec", "lemma-nagata-final-fp-envelope", "lemma-nagata-scheme-image-of-closed-immersion", "lemma-nagata-scheme-image-restrict-open", "lemma-nagata-scheme-image-universal", "prop-nagata-closed-subscheme-compactifiable"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

The constructed map $j_f\colon X\to\overline X_f$ is a quasi-compact open
immersion.

## Proof

Restrict the scheme-theoretic image defining $\overline X_f$ to the open
$X_f^{\mathrm{fp}}$ in the ambient compactification. By
[lemma-nagata-scheme-image-restrict-open], this restriction is
canonically isomorphic to the image of the closed immersion
$X\hookrightarrow X_f^{\mathrm{fp}}$. The latter image is canonically
isomorphic to $X$ by
[lemma-nagata-scheme-image-of-closed-immersion]; transport the
open-immersion structure across this specified isomorphism. The resulting
square with $X_f^{\mathrm{fp}}\hookrightarrow \overline X_f^{\mathrm{fp}}$ is cartesian by the image-restriction
comparison, so $j_f$ is its base change. Quasi-compactness is preserved by
this base change.
