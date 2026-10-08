+++
id = "lem-pur-co-smooth-composition"
kind = "lemma"
title = "Composition"
order = 1993
uses = ["def-pur-co-smoothness", "def-pur-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-exceptional-inverse-image"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
if $f:X\to Y$ and $g:Y\to Z$ are cohomologically smooth, then
$gf:X\to Z$ is cohomologically smooth, and moreover

$$
\omega_{gf}\;\cong\;\omega_f\otimes^L_{\Lambda_X}Lf^*\omega_g.
$$

## Proof

The three conditions to verify are those of [def-pur-co-smoothness]; pullback and tensor commute by the canonical reassociation in [def-weil-derived-pullback-tensor-hom].
Using the composition rule $R(gf)^!\simeq Rf^!Rg^!$ of
[def-weil-exceptional-inverse-image] for the two tensor formulas:

$$
R(gf)^!K
\;\simeq\;Lf^*\bigl(Lg^*K\otimes^L\omega_g\bigr)\otimes^L\omega_f
\;\simeq\;L(gf)^*K\otimes^L\bigl(\omega_f\otimes^LLf^*\omega_g\bigr).
$$

The tensor product in the parentheses is invertible (a product of
invertible objects of [def-weil-derived-tensor]), which gives (1)
and (2) for $gf$; the same calculation after arbitrary base change
gives (3).
