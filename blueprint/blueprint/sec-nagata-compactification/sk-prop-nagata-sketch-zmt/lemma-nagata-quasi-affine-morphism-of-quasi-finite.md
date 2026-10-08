+++
id = "lemma-nagata-quasi-affine-morphism-of-quasi-finite"
kind = "lemma"
title = "A quasi-finite morphism is quasi-affine"
order = 187
lean = ["AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite"]
uses = ["def-nagata-quasi-affine-morphism", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-zmt-quasi-affine-source"]
+++
Let $f\colon X\to Y$ be separated, quasi-compact, locally quasi-finite and
locally of finite type. Then $f$ is quasi-affine in the sense of
[def-nagata-quasi-affine-morphism]. No hypothesis on $Y$ is needed.

## Proof

Let $Y'\subseteq Y$ be an affine open. All four hypotheses are stable under
restricting the base to an open subscheme, so $f^{-1}(Y')\to Y'$ is again
separated, quasi-compact, locally quasi-finite and locally of finite type.
Its target $Y'$ is affine, hence quasi-affine, so
[lemma-nagata-zmt-quasi-affine-source] makes $f^{-1}(Y')$ a quasi-affine
scheme.
