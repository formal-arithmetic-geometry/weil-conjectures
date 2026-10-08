+++
id = "rem-exc-mate-does-not-preserve-isomorphism"
kind = "remark"
title = "The mate of the base-change comparison is not a criterion"
order = 1785
+++
Passing to the mate under an adjunction does *not* preserve
isomorphisms: for an adjunction $F\dashv G$ a map $FA\to B$ can be an
isomorphism while its transpose $A\to GB$ is not, and conversely, since
the unit and the counit intervening need not be isomorphisms. In
particular the base-change comparison
$\beta:Lg'^*Rf^{\times}\to Rf'^{\times}Lg^*$ cannot be tested for
isomorphy by testing its adjoint under $Rf'_!\dashv Rf'^{\times}$, and a
criterion of that shape is invalid. This is visible already for
$f=\operatorname{id}_Y$ and an open immersion $g:Y'\hookrightarrow Y$:
the comparison is the identity of $Lg^*K$, an isomorphism, while its
transpose under the adjunctions $Rf'_!\dashv Rf'^{\times}$ and
$Lg^*\dashv Rg_*$ is the composite of the counit (the identity) with the
unit of $Lg^*\dashv Rg_*$, i.e. the localization unit
$K\to Rg_*Lg^*K$, which is not an isomorphism (for $K=\Lambda$ its
cokernel is the skyscraper at the boundary).
