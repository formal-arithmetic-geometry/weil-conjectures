+++
id = "def-nagata-composition-of-blowups-comparison"
kind = "definition"
title = "Comparison for a composite of arbitrary blow-ups"
order = 134
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comp"]
uses = ["cor-nagata-blowup-product-common-refinement", "def-nagata-blowup-product-comparison", "def-nagata-blowup-product-domination-maps", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-invertible-ideal", "def-nagata-proj-closed-center-finite-degree", "lemma-nagata-blowup-invertible-factor", "lemma-nagata-composition-center-ideal", "lemma-nagata-invertible-ideal-tensor-power", "lemma-nagata-product-ideal-common-blowup", "prop-nagata-global-blowup-cover-independent", "thm-nagata-blowup-principalizes-center", "thm-nagata-blowup-product-ideal", "thm-nagata-blowup-universal-property"]
+++
Let $X$, $\mathcal I$, $X'$, $b$, $Z'$, $d$, and $\mathcal J(Z')$ be as in
[lemma-nagata-composition-center-ideal], and let the second blow-up be
centred at $Z'\hookrightarrow X'$. Let $E$ be the exceptional divisor of
$b$ and let $\mathcal I_E$ be its invertible ideal; write
$\mathcal I_{Z'}$ for the ideal defining $Z'$. Form the explicit ideal
$\mathcal K(Z')=\mathcal I\mathcal J(Z')$ on $X$. The extended ideal on
$X'$ is $\mathcal I_E^d\mathcal I_{Z'}$. Define

$$
\Omega_{Z,Z'}\colon
\operatorname{Bl}_{\mathcal I_{Z'}}(X')
\longrightarrow
\operatorname{Bl}_{\mathcal K(Z')}(X)
$$

as the product-blow-up comparison followed by the comparison which removes
the invertible factor $\mathcal I_E^d$. Define the reverse map by the
corresponding universal lifts.
