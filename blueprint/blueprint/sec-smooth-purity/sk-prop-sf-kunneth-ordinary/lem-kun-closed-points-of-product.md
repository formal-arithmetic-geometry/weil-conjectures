+++
id = "lem-kun-closed-points-of-product"
kind = "lemma"
title = "Closed points of a product"
order = 1745
uses = ["def-kun-support", "def-weil-pbc-scheme-conventions", "lem-kun-closed-point-field"]
+++
Let $X$ and $Y$ be schemes of finite type over a field $K$ and
$z\in X\times_KY$ with images $x\in X$ and $y\in Y$. Then $z$
is a closed point of $X\times_KY$ if and only if $x$ and $y$ are
closed points.

## Proof

By [lem-kun-closed-point-field], $z$ is closed iff
$\kappa(z)$ is finite over $K$, and $\kappa(x)$, $\kappa(y)$
are then finitely generated subfields of $\kappa(z)$, hence finite
over $K$ (a subfield of a finite extension is finite), so $x,y$
are closed. Conversely, if $\kappa(x)$ and $\kappa(y)$ are finite
over $K$, then $\kappa(x)\otimes_K\kappa(y)$ is a finite
dimensional $K$-algebra, presented as a finite product of Artinian
local rings; the residue field $\kappa(z)$ of the point $z$ over
$(x,y)$ is a residue field of that finite algebra, hence finite over
$K$, so $z$ is closed.
