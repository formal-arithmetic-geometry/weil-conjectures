+++
id = "lemma-nagata-invertible-ideal-is-effective-cartier"
kind = "lemma"
title = "An invertible ideal is effective Cartier"
order = 99
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isEffectiveCartierCenter"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-invertible-ideal"]
+++
An invertible ideal sheaf, viewed as an ideal by its specified inclusion into
the structure sheaf, is an effective Cartier ideal.

## Proof

On an open set where the invertible ideal is free with basis $a$, the map
$\mathcal O_X\to\mathcal I$ sending $1$ to $a$ is an isomorphism. The
inclusion $\mathcal I\hookrightarrow\mathcal O_X$ is injective because
$\mathcal I$ is an ideal submodule, so the composite
$\mathcal O_X\to\mathcal O_X$ is multiplication by $a$ and is injective.
Thus $a$ is a non-zero-divisor on every member of this cover, which is
exactly the effective-Cartier condition.
