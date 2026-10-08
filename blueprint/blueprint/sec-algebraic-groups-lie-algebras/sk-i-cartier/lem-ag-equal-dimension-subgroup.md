+++
id = "lem-ag-equal-dimension-subgroup"
kind = "lemma"
title = "A closed subgroup of full dimension is everything"
order = 2490
uses = ["lem-wf-affine-dimension-drop"]
+++
Let $G\subseteq\operatorname{GL}(V)$ be an irreducible closed matrix
group over $\overline{\mathbf Q}_\ell$, and let $J\subseteq G$ be a
closed subgroup with $\dim J=\dim G$. Then $J=G$.

## Proof

The closed subset $J$ of the finite-type variety $G$ has finitely many
irreducible components, and its dimension is the maximum of their
dimensions, so some irreducible component $J_1$ of $J$ has
$\dim J_1=\dim G$. The matrix group $G$ is closed in the affine variety
$\operatorname{GL}(V)$, hence is an irreducible affine variety. If
$J_1\subsetneq G$, then [lem-wf-affine-dimension-drop] would give
$\dim J_1\le\dim G-1$; hence the closed subset $J_1$ equals $G$. Thus
$G=J_1\subseteq J\subseteq G$, and $J=G$.
