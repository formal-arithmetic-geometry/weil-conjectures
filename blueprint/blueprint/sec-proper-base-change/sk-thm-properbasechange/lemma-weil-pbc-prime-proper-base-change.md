+++
id = "lemma-weil-pbc-prime-proper-base-change"
kind = "lemma"
title = "Prime-coefficient proper base change"
order = 1313
uses = ["def-weil-pbc-property", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-projective-line", "prop-weil-pbc-reduction-to-projective-line"]
+++
Every proper morphism satisfies proper base change for sheaves of
$\mathbf F_\ell$-modules.

## Proof

The projective-line proposition supplies the sole geometric input required by
the S3 reduction. Finite morphisms, composition, and cancellation in that
reduction preserve the named S0 exchange map, so the resulting isomorphism is
the exchange map for the original proper morphism.

## Detailed form

For every prime $r$, every proper $f:X\to Y$ (no finite-presentation
hypothesis), every cartesian base change, and every sheaf $F$ of $\mathbf
F_r$-modules on $X_{\Et}$, the specified map

$$
 g^{-1}Rf_*F\xrightarrow{\sim}Rf'_*g'^{-1}F
$$

is an isomorphism.

## Proof

The projective-line proposition [prop-weil-pbc-projective-line]
supplies the hypothesis of the reduction proposition
[prop-weil-pbc-reduction-to-projective-line], and that proposition
yields $\mathrm{PBC}(f)$ for every proper $f$ in the sense of
[def-weil-pbc-property]; the displayed map is exactly the exchange morphism of
that property, hence an isomorphism.
