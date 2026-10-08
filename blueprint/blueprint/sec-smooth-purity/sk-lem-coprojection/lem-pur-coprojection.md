+++
id = "lem-pur-coprojection"
kind = "lemma"
title = "Co-projection for a closed immersion"
order = 2006
uses = ["def-exchange-projection", "def-pur-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $i:Z\hookrightarrow W$ be a
closed immersion, let
$K$ be an object on $W$ and $L$ an invertible object on $W$. Then
the canonical co-projection

$$
Ri^!(K\otimes^L_{\Lambda_W}L)\xrightarrow{\ \sim\ }Ri^!K\otimes^L_{\Lambda_Z}Li^*L
$$

is an isomorphism.

## Proof

For a test object $A$ on $Z$, tensor-Hom adjunction, the projection
formula of [def-exchange-projection] for $Ri_!$, and the inverse
of $L$ identify maps $A\to Ri^!(K\otimes^LL)$ with maps
$Ri_!(A\otimes^LLi^*L^{-1})\to K$; Yoneda gives the assertion.
