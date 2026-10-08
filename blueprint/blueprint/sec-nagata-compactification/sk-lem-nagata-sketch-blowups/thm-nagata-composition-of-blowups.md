+++
id = "thm-nagata-composition-of-blowups"
kind = "theorem"
title = "[stacks-project]"
order = 135
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp"]
uses = ["cor-nagata-blowup-cartier-iso", "cor-nagata-blowup-product-common-refinement", "def-nagata-blowup-product-comparison", "def-nagata-blowup-product-domination-maps", "def-nagata-composition-of-blowups-comparison", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "def-nagata-proj-closed-center-finite-degree", "lemma-nagata-blowup-invertible-factor", "lemma-nagata-composition-center-ideal", "lemma-nagata-composition-extended-ideal-equality", "lemma-nagata-invertible-ideal-tensor-power", "lemma-nagata-product-ideal-common-blowup", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-product-ideal", "thm-nagata-blowup-universal-property"]
+++
With $Z=V(\mathcal I)$ as above, the two constructed comparison maps are
inverse over $X$. Hence the
composite is the blow-up of the finite-presentation center
$Y(Z')=V(\mathcal K(Z'))\hookrightarrow X$, whose support satisfies

$$
|Y(Z')|=|Z|\cup b(|Z'|).
$$

## Proof

Put $X_1=\operatorname{Bl}_{\mathcal I}(X)$ and
$\mathcal J'=\mathcal J\mathcal O_{X_1}$. By the extended-ideal equality,
$\mathcal J'=\mathcal I_E^d\mathcal I_{Z'}$. The product-ideal comparison
[thm-nagata-blowup-product-ideal] therefore gives an isomorphism over
$X$

$$
\operatorname{Bl}_{\mathcal J'}(X_1)
\xrightarrow{\sim}\operatorname{Bl}_{\mathcal I\mathcal J}(X).
$$

Since $\mathcal I_E^d$ is invertible, the invertible-factor comparison
[lemma-nagata-blowup-invertible-factor] gives a canonical isomorphism
$\operatorname{Bl}_{\mathcal I_{Z'}}(X_1)\cong \operatorname{Bl}_{\mathcal J'}(X_1)$. Their composite is the map
$\Omega_{Z,Z'}$ in the definition; the reverse composite of the inverse
comparisons is the stated reverse map.

For completeness, these maps are the universal lifts for the same quotient:
on the iterated blow-up the product of the tautological invertible quotients
is the tautological quotient of $\mathcal I\mathcal J$, while on the
$\mathcal I\mathcal J$-blow-up its two factor quotients give the tautological
quotients for $\mathcal I$ and for $\mathcal J'$; multiplying by the inverse
of the local generator of $\mathcal I_E^d$ gives the quotient for
$\mathcal I_{Z'}$. Thus each composite is an $X$-morphism inducing the
original tautological quotient. Uniqueness in the blow-up universal
property, first over $X$ and then over $X_1$, makes both composites identities.
The center ideal $\mathcal K=\mathcal I\mathcal J$ is finite type, hence
defines a finite-presentation closed immersion, and
[lemma-nagata-composition-center-ideal] gives its support as
$|V(\mathcal I)|\cup b(|Z'|)$.
