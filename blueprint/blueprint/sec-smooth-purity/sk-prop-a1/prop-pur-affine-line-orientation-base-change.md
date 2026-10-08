+++
id = "prop-pur-affine-line-orientation-base-change"
kind = "theorem"
title = "Base change of the global orientation"
order = 1953
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-pur-affine-line-datum", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-exceptional-adjoint-admissibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-gysin-structure", "lem-pur-kummer-coefficient-base-change", "prop-pur-affine-line-orientation-uniqueness", "thm-pur-affine-line-orientation", "thm-pur-rank-one-local-calculation"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$\Lambda=A$. For every morphism $v:Y'\to Y$, with $s'$ the zero
section of $\mathbf A^1_{Y'}$, the
exceptional
base-change comparison identifies $Lv^*\operatorname{pur}_s$ with the
orientation $\operatorname{pur}_{s'}$ for $\mathbf A^1_{Y'}$ of
[thm-pur-affine-line-orientation].

## Proof

Both $Lv^*\operatorname{pur}_s$ and $\operatorname{pur}_{s'}$ are morphisms
$\Lambda_{Y'}\to Rs'^!\Lambda_{\mathbf A^1_{Y'}}(1)[2]$: the source and
target of the first are transported by the exceptional base-change
comparison of [def-weil-exceptional-adjoint-admissibility] (the
base change of a closed immersion is a closed immersion and the
affine-line datum base-changes, by [lem-pur-gysin-structure] and
[def-pur-affine-line-datum]). Its pullback to a geometric point
$\bar y'$ of $Y'$ is the pullback of the normalization class
$1$: the Kummer class is compatible with the pullback
([lem-pur-kummer-coefficient-base-change]) and the rank-one
calculation is the one of [thm-pur-rank-one-local-calculation]
transported along $Y'\to Y$, using $s'(\bar y')=s(\bar y)$ with
$\bar y=v(\bar y')$. Hence, by the normalization of
[thm-pur-affine-line-orientation] and the uniqueness of
[prop-pur-affine-line-orientation-uniqueness], the two morphisms
coincide.
