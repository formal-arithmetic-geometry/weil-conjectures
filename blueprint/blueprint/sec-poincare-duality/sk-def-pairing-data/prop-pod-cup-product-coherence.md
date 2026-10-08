+++
id = "prop-pod-cup-product-coherence"
kind = "theorem"
title = "Coherence of the mixed-support cup product"
order = 2417
tags = ["latex:proposition"]
uses = ["cor-cbc-proper-coincidence", "def-exchange-projection", "def-weil-derived-direct-image", "def-weil-derived-tensor", "fix-prop-adjunctions", "fix-prop-projection-formula"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), mixed-support cup product is natural in $K$ and $L$, and satisfies the associativity identity on $R\Gamma _c(X,K)\otimes R\Gamma (X,L)\otimes R\Gamma (X,M)$; the unit element $1\in H^0(X,A)$ acts as the identity after the canonical identifications; and the compatibility with the iterate of the cup product and with the identification $R\Gamma _c(X,-)\cong R\Gamma (X,-)$ for a proper $X$ holds.

## Proof

The cup product is the composite of the projection transformation of
[def-exchange-projection] and the direct-image counit of
[def-weil-derived-direct-image]; both are natural.
The tensor associator and unit in [def-weil-derived-tensor],
the composite-counit identity of [fix-prop-adjunctions], and
the projection coherence of [fix-prop-projection-formula]
identify the two parenthesizations of the triple product.
The same identities with a unit factor prove the unit assertion.
If $a_X$ is proper, [cor-cbc-proper-coincidence] identifies
$Ra_{X!}$ with $Ra_{X*}$, using the identity compactification.
Under this comparison the projection map and counit are the same
maps, so the supported and ordinary cup products agree.
