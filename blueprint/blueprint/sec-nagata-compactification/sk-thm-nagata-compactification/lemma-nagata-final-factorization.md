+++
id = "lemma-nagata-final-factorization"
kind = "lemma"
title = "Factorization equality for the final candidate"
order = 406
uses = ["def-nagata-final-compactification", "def-nagata-scheme-image-factor", "lemma-nagata-final-compactification-spec", "lemma-nagata-final-fp-envelope", "lemma-nagata-scheme-image-universal"]
+++
**Status.** Bypassed by the formalized route: the final assembly is carried
out inside `AlgebraicGeometry.NagataCompactification` and
`AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`,
which produce the factorization and its three properties directly, without
separately named intermediate objects.

The constructed maps in
[def-nagata-final-compactification] satisfy $p_f\circ j_f=f$.

## Proof

Put $g=j_f^{\mathrm{fp}}\circ i_f^{\mathrm{fp}}$, write
$g^{\mathrm{im}}\colon X\to\operatorname{SIm}(g)$ for its image factor and
$g_{\mathrm{im}}\colon\operatorname{SIm}(g)\hookrightarrow \overline X_f^{\mathrm{fp}}$ for the image inclusion, and write
$\overline p_f\colon\overline X_f^{\mathrm{fp}}\to S$ for the ambient map.
Then

$$
p_f\circ j_f
=\overline p_f\circ g_{\mathrm{im}}\circ g^{\mathrm{im}}
=\overline p_f\circ g
=\overline p_f\circ j_f^{\mathrm{fp}}\circ i_f^{\mathrm{fp}}
=f.
$$

The second equality is the scheme-image factorization; the last is the
factorization equality for the compactification of the finite-presentation
envelope followed by the equality defining $i_f^{\mathrm{fp}}$ over $S$.
