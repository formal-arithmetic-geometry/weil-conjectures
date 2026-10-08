+++
id = "lemma-nagata-diagonal-mixed-open"
kind = "lemma"
title = "The diagonal on a mixed open"
order = 235
lean = ["AlgebraicGeometry.diagonalRestrictChartArrowIso"]
+++
Let $X=U\cup V$ be an open cover over $S$. The pullback of
$\Delta_{X/S}$ to $U\times_SV$ is canonically the map

$$
U\cap V\longrightarrow U\times_SV.
$$

The analogous assertion holds over $V\times_SU$.

## Proof

Both schemes represent triples consisting of a point of $U$, a point of
$V$, and an equality of their images in $X$. The canonical isomorphism is
obtained from the universal property of the pullback.
