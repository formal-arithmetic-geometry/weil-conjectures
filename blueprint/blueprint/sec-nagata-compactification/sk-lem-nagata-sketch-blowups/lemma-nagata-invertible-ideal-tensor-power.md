+++
id = "lemma-nagata-invertible-ideal-tensor-power"
kind = "lemma"
title = "Tensor powers of an invertible ideal"
order = 106
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pow"]
uses = ["def-nagata-effective-cartier-ideal", "def-nagata-invertible-ideal", "lemma-nagata-invertible-ideal-is-effective-cartier"]
+++
If $\mathcal L\subseteq\mathcal O_Y$ is an invertible ideal, then for every
$n\geq0$ the multiplication map

$$
\mathcal L^{\otimes n}\longrightarrow\mathcal L^n
$$

is an isomorphism.

## Proof

By [lemma-nagata-invertible-ideal-is-effective-cartier], work on an
open cover where $\mathcal L=(a)$ with $a$ a non-zero-divisor. The source
has basis $a^{\otimes n}$ and the target has basis $a^n$; multiplication
sends the first basis to the second. Hence it is an isomorphism on this
cover, and is therefore an isomorphism of sheaves.
