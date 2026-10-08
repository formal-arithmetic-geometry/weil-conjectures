+++
id = "def-nagata-relative-affine-space"
kind = "definition"
title = "Relative affine space"
order = 181
lean = ["AlgebraicGeometry.AffineSpace"]
+++
For a scheme $S$ and $n\in\mathbb N$, define

$$
\mathbb A^n_S=\operatorname{Spec}_S
\bigl(\operatorname{Sym}_{\mathcal O_S}(\mathcal O_S^{\oplus n})\bigr).
$$

Concretely, on an affine open $V=\operatorname{Spec}(R)$ of $S$ this is
$\operatorname{Spec}(R[T_1,\ldots,T_n])$; for a principal restriction
$D(a)\subseteq V$ the transition map is induced by
$R[T_1,\ldots,T_n]\to R_a[T_1,\ldots,T_n]$.
