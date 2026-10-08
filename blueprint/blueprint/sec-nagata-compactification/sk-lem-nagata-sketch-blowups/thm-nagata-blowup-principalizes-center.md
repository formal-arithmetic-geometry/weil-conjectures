+++
id = "thm-nagata-blowup-principalizes-center"
kind = "theorem"
title = "Principalization of the center ideal"
order = 102
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_comap_blowupMap"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-chart-map", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-effective-cartier-ideal", "def-nagata-extended-ideal", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-invertible-ideal", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-chart-extended-ideal-principal", "lemma-nagata-chart-generator-regular", "lemma-nagata-chart-generators-associated", "lemma-nagata-extended-ideal-affine-chart", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-one-element", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-generators-cover-proj", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-chart", "prop-nagata-affine-blowup-chart-cover", "prop-nagata-global-blowup-cover-independent", "prop-nagata-proj-standard-open", "prop-nagata-rees-graded"]
+++
If $\mathcal I$ is a finite type quasi-coherent ideal on $X$, then on
$\operatorname{Bl}_{\mathcal I}(X)$ the extended ideal
$\mathcal I\mathcal O_{\operatorname{Bl}_{\mathcal I}(X)}$ is locally
principal, generated locally by a non-zero-divisor, and hence is an
invertible ideal defining an effective Cartier divisor.

## Proof

Work locally on an arbitrary affine open of $X$. Finite type of
$\mathcal I$ gives finitely many generators on that affine, and the
corresponding standard charts cover its blow-up. Use
[lemma-nagata-chart-extended-ideal-principal] and
[lemma-nagata-chart-generator-regular]. The local principal ideals
glue because their generators differ by units by
[lemma-nagata-chart-generators-associated].
