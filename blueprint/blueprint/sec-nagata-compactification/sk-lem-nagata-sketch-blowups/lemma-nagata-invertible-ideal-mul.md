+++
id = "lemma-nagata-invertible-ideal-mul"
kind = "lemma"
title = "Product of invertible ideals is invertible"
order = 118
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.mul"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-invertible-ideal", "lemma-nagata-invertible-ideal-is-effective-cartier"]
+++
The product of two invertible ideal sheaves is invertible.

## Proof

By [lemma-nagata-invertible-ideal-is-effective-cartier], local bases of
the two ideals are regular elements $a$ and $b$. Their product is generated
by $ab$, which is regular because multiplication by $a$ and by $b$ are
injective. These local generators give the required rank-one bases.
