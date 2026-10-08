+++
id = "lemma-nagata-blowup-invertible-factor"
kind = "lemma"
title = "Blow-up is unchanged after multiplying by an invertible factor"
order = 131
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_isInvertible_iso"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "lemma-nagata-cartier-total-transform-blowup", "lemma-nagata-ideal-invertible-product-factor", "lemma-nagata-invertible-ideal-mul", "lemma-nagata-invertible-product-factor", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-universal-property"]
+++
Let $X$ be a scheme, let $\mathcal L$ be an invertible ideal on $X$, and
let $\mathcal J$ be a quasi-coherent ideal (finite-typeness is not needed).
Then the blow-ups of $\mathcal L\mathcal J$ and of $\mathcal J$ are
canonically isomorphic over $X$.

## Proof

Tensor the tautological quotient for $\mathcal J$ with the pullback of the
invertible ideal $\mathcal L$ to obtain an invertible quotient of
$\mathcal L\mathcal J$; this gives a lift from
$\operatorname{Bl}_{\mathcal J}(X)$ to
$\operatorname{Bl}_{\mathcal L\mathcal J}(X)$. Conversely, tensor the
tautological quotient of $\mathcal L\mathcal J$ with the dual of the
pulled-back invertible module $\mathcal L$. The evaluation isomorphism
gives an invertible quotient of $\mathcal J$ and hence a reverse lift.
Locally this is division by a basis of $\mathcal L$, so the quotient maps
are compatible with the specified ideal inclusions and glue independently
of the chosen bases. Both composites induce the original tautological
quotient, so uniqueness in
[thm-nagata-blowup-universal-property] makes them identities.
