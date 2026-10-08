+++
id = "cor-nagata-blowup-product-common-refinement"
kind = "theorem"
title = "Common refinement by the product ideal"
order = 125
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_iso"]
tags = ["latex:corollary"]
uses = ["def-nagata-blowup-product-domination-maps", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "lemma-nagata-cartier-total-transform-blowup", "lemma-nagata-ideal-invertible-product-factor", "lemma-nagata-invertible-ideal-mul", "lemma-nagata-invertible-product-factor", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-product-ideal", "thm-nagata-blowup-universal-property", "thm-nagata-global-blowup-complement"]
+++
The constructed $d_{\mathcal I}$ and $d_{\mathcal J}$ are morphisms over
$X$. If both ideals restrict to the unit ideal on an open $U$, the product
blow-up and both maps restrict to the identity over $U$.

## Proof

The maps are composites over $X$ by definition. On $U$, all three ideals
are the unit ideal, so all three blow-ups are identified with $U$ by the
complement theorem. The universal maps are unique over $U$, hence become
the identity under these identifications.
