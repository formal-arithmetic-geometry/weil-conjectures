+++
id = "thm-nagata-global-blowup-complement"
kind = "theorem"
title = "Complement of the center"
order = 59
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupMap_restrict_support_compl"]
uses = ["def-nagata-global-blowup", "lemma-nagata-affine-blowup-complement", "lemma-nagata-ideal-unit-off-support", "prop-nagata-global-blowup-cover-independent"]
+++
Let $U=X\setminus V(\mathcal I)$. The restriction

$$
b_{X,\mathcal I}^{-1}(U)\longrightarrow U
$$

is an isomorphism.

## Proof

Cover $X$ by affine opens. Under
[prop-nagata-global-blowup-cover-independent], the restriction over each
affine is the affine complement isomorphism of
[lemma-nagata-affine-blowup-complement]. These local isomorphisms glue,
and isomorphisms are local on source and target.
