+++
id = "lem-fin-coordinate-generic-dimension"
kind = "lemma"
title = "Coordinate projections lower generic dimension"
order = 1633
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $S$ be integral with function field $K$, let
$Y\hookrightarrow\mathbf A^m_S$ be a closed immersion, and let
$X\subset Y$ be open. If $\dim X_K\leq n$, then for every
coordinate $t_r:X\to\mathbf A^1_S$, the fiber over the generic
point of $\mathbf A^1_S$ has dimension at most $n-1$.
An empty fiber is assigned dimension $-\infty$.
The notation refers to scheme conventions.

## Proof

Use the generic-fiber convention of
[def-weil-pbc-scheme-conventions]. A component of $X_K$
on which $t_r$ is algebraic over $K$ does not dominate
$\mathbf A^1_K$, so it contributes no generic fiber.
On each remaining irreducible component with function field $E$,
$t_r$ is transcendental over $K$. The elementary dimension
formula for a finitely generated field extension gives

$$
\operatorname{trdeg}_{K(t_r)}E
=\operatorname{trdeg}_K E-1\leq n-1.
$$

This is the dimension of its generic fiber. Taking the maximum
over the finitely many components gives the assertion. Nilpotents
do not change these dimensions.
