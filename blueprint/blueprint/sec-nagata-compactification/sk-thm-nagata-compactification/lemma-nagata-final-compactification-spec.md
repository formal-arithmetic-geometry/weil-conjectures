+++
id = "lemma-nagata-final-compactification-spec"
kind = "lemma"
title = "Components of the final compactification candidate"
order = 403
uses = ["def-nagata-closed-subscheme-compactification", "def-nagata-final-compactification", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-universal"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

The ambient scheme $\overline X_f$ is the scheme-theoretic image of the
composite
$X\to X_f^{\mathrm{fp}}\to\overline X_f^{\mathrm{fp}}$. The map
$j_f$ is its canonical image factor and $p_f$ is the restriction of the
ambient structural morphism. These identifications commute with the
displayed factorization over $S$.

## Proof

Unfold $\mathsf{Closed}$ in
[def-nagata-final-compactification]. Its ambient object is defined as
`Scheme.Hom.image` of the stated composite, and its first map is
`Scheme.Hom.toImage`; the factorization equality is
[lemma-nagata-scheme-image-universal]. The last map is obtained by
restricting the already specified map
$\overline X_f^{\mathrm{fp}}\to S$, so the two identifications are
compatible with the structural morphisms by the same factorization
equality.
