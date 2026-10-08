+++
id = "lemma-nagata-invertible-product-factor"
kind = "lemma"
title = "[stacks-project]"
order = 120
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.of_mul_left"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-invertible-ideal", "lemma-nagata-ideal-invertible-product-factor"]
+++
Let $X$ be a scheme and let $\mathcal I,\mathcal J$ be quasi-coherent
ideals on $X$. If the product
$\mathcal I\mathcal J$ defines an effective Cartier divisor, then each of
$\mathcal I$ and $\mathcal J$ defines an effective Cartier divisor.

## Proof

Work on affine opens and apply
[lemma-nagata-ideal-invertible-product-factor] to the corresponding
ideals. The resulting local invertible-module structures and regular
generators are compatible under localization, so both ideal sheaves define
effective Cartier divisors.
