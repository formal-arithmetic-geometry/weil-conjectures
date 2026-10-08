+++
id = "thm-nagata-blowup-product-ideal"
kind = "theorem"
title = "[stacks-project]"
order = 123
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_mul_iso"]
uses = ["def-nagata-blowup-product-comparison", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "lemma-nagata-cartier-total-transform-blowup", "lemma-nagata-effective-cartier-is-invertible", "lemma-nagata-ideal-invertible-product-factor", "lemma-nagata-invertible-ideal-mul", "lemma-nagata-invertible-product-factor", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-universal-property"]
+++
The constructed maps $\Phi_{\mathcal I,\mathcal J}$ and
$\Psi_{\mathcal I,\mathcal J}$ are inverse over $X$. Thus the iterated
blow-up is identified with the blow-up of $\mathcal I\mathcal J$.

## Proof

Write $p\colon X_{\mathcal I,\mathcal J}\to X$ for the composite and
$q\colon\operatorname{Bl}_{\mathcal I\mathcal J}(X)\to X$ for the
product blow-up. The construction of $\Phi_{\mathcal I,\mathcal J}$ is
the unique $X$-morphism whose pullback of the tautological invertible
quotient on the product blow-up is the product of the two tautological
quotients on $X_{\mathcal I,\mathcal J}$. Conversely, the construction of
$\Psi_{\mathcal I,\mathcal J}$ first uses the invertible quotient
$q^*\mathcal I$ and then the invertible quotient of the pullback of
$\mathcal J$; their product is the tautological quotient of
$q^*(\mathcal I\mathcal J)$. Thus both composites are $X$-morphisms
pulling back the relevant tautological quotient to itself. Apply uniqueness
in [thm-nagata-blowup-universal-property] first for the product
blow-up to obtain $\Phi\circ\Psi=\mathrm{id}$. For the other composite,
first apply uniqueness for the $\mathcal I$-blow-up to see that its
projection to $\operatorname{Bl}_{\mathcal I}(X)$ is the original first
projection. It is therefore a morphism over
$\operatorname{Bl}_{\mathcal I}(X)$, and uniqueness for the second blow-up
gives $\Psi\circ\Phi=\mathrm{id}$.
