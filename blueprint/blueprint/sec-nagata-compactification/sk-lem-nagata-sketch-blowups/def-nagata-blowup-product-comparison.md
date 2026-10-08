+++
id = "def-nagata-blowup-product-comparison"
kind = "definition"
title = "Comparison maps for the product-ideal blow-up"
order = 122
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_iso"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "lemma-nagata-cartier-total-transform-blowup", "lemma-nagata-effective-cartier-is-invertible", "lemma-nagata-ideal-invertible-product-factor", "lemma-nagata-invertible-ideal-mul", "lemma-nagata-invertible-product-factor", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-universal-property"]
+++
Let $X$ be a scheme and let $\mathcal I,\mathcal J$ be finite-type
quasi-coherent ideals on $X$. Let $X_{\mathcal I,\mathcal J}$ be the
scheme obtained by first blowing up $\mathcal I$ and then the extended
ideal $\mathcal J\mathcal O_{\operatorname{Bl}_{\mathcal I}(X)}$ from
[def-nagata-extended-ideal].
The first exceptional ideal is Cartier after the first blow-up. Applying
[lemma-nagata-cartier-total-transform-blowup] on the second blow-up
(chartwise, where the pulled-back local equation remains regular) shows
that its total transform is invertible. This is the special total-transform
input; no assertion about arbitrary images of invertible ideals is used.
On this iterated blow-up, the total transform
of the first exceptional ideal is invertible, and the second exceptional
ideal is invertible by [thm-nagata-blowup-principalizes-center].
Hence their product, which is the extension of
$\mathcal I\mathcal J$, is invertible by
[lemma-nagata-invertible-ideal-mul]; define

$$
\Phi_{\mathcal I,\mathcal J}\colon
X_{\mathcal I,\mathcal J}
\longrightarrow\operatorname{Bl}_{\mathcal I\mathcal J}(X)
$$

by the universal-lift construction for their product. On
$\operatorname{Bl}_{\mathcal I\mathcal J}(X)$, factor the invertible
product first through the $\mathcal I$-blow-up. The extension of
$\mathcal I\mathcal J$ is an effective Cartier ideal, so
[lemma-nagata-invertible-product-factor] and
[lemma-nagata-effective-cartier-is-invertible] make the extensions
of both factors invertible. The universal lift for $\mathcal I$, followed
by the universal lift for the extended $\mathcal J$, defines the resulting
map

$$
\Psi_{\mathcal I,\mathcal J}\colon
\operatorname{Bl}_{\mathcal I\mathcal J}(X)
\longrightarrow X_{\mathcal I,\mathcal J}.
$$
