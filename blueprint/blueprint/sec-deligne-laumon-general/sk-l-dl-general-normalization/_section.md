+++
id = "sk-l-dl-general-normalization"
kind = "section"
title = "Generic relative Noether normalization"
order = 2822
lean = ["AlgebraicGeometry.exists_dense_isFinite_toIteratedAffineLine"]
uses = ["sk-i-real-normalization"]
+++
*Lemma (sketch).*

Let $f_0:X_0\to Y_0$ be a dominant affine morphism of integral schemes,
with generic relative dimension $r$. After shrinking $Y_0$ and taking
its inverse image in $X_0$, there is a factorization

$$
X_0\xrightarrow{\nu_0}\mathbf A^r_{Y_0}
\xrightarrow{\pi_0}Y_0,
\qquad \nu_0\text{ finite}.
$$

The projection $\pi_0$ is a composition of $r$ affine-line projections.

## Proof

Over the function field of $Y_0$, apply Noether normalization to the
coordinate algebra of the generic fiber. The algebraic argument in
[sk-i-real-normalization], before its final dimension-one
specialization, gives a finite algebra over a polynomial ring in $r$
variables. Clear the finitely many denominators in these variables and
the monic integral relations by shrinking the affine base. This spreads
out the finite map; dropping one coordinate at a time factors $\pi_0$.

Uses: [sk-i-real-normalization]
