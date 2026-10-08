+++
id = "def-nagata-sheaf-rees-algebra"
kind = "definition"
title = "Sheaf Rees algebra"
order = 105
uses = ["lemma-nagata-sheaf-ideal-powers-assoc"]
+++
**Status.** Bypassed by the formalized route: no separate relative-Proj
primitive was formalized. The blow-up is glued from the affine Proj charts
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`,
`AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`) with
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`.

Let $\mathcal I\subseteq\mathcal O_X$ be a quasi-coherent ideal sheaf. Define
its sheaf Rees algebra by

$$
\mathcal R_X(\mathcal I)=\bigoplus_{n\geq0}\mathcal I^n,
$$

with multiplication induced by the canonical multiplication maps
$\mathcal I^m\otimes_{\mathcal O_X}\mathcal I^n\to \mathcal I^{m+n}$ and unit the degree-zero copy of $\mathcal O_X$.
The direct sum is taken in sheaves of $\mathcal O_X$-modules. Define
multiplication on homogeneous summands by the displayed maps and extend it
by the universal property of the direct sum; the degree-zero inclusion is
the unit. Associativity and the unit laws are exactly
[lemma-nagata-sheaf-ideal-powers-assoc], so this is a graded
quasi-coherent $\mathcal O_X$-algebra. The multiplication maps need not be
injective, and no such hypothesis is used.
