+++
id = "lemma-nagata-strict-chart-map-surjective"
kind = "lemma"
title = "Surjectivity onto the extended-ideal chart"
order = 148
lean = ["AlgebraicGeometry.AffineBlowup.closure_range_awayAlgebraMap_union_range_awayMap"]
uses = ["def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "def-nagata-strict-chart-to-extended-blowup-chart", "lemma-nagata-chart-ring-normal-form", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "lemma-nagata-strict-chart-to-extended-blowup-chart", "prop-nagata-rees-graded"]
+++
The constructed homomorphism $\sigma_a$ is surjective.

## Proof

By [lemma-nagata-chart-ring-normal-form], the target is generated as a
$B$-algebra by the fractions $z/b$ with $z\in J$. Write
$z=\sum_k y_k\overline{x_k}$ with $x_k\in I$. Then

$$
z/b=\sum_k\sigma_a\bigl(y_k\otimes(x_k/a)\bigr),
$$

proving surjectivity.
