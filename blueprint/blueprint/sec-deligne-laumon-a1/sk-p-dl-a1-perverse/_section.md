+++
id = "sk-p-dl-a1-perverse"
kind = "section"
title = "Fourier exactness on a curve"
order = 2737
uses = ["sk-d-dl-a1-setup", "sk-l-dl-a1-endpoints", "sk-prop-kernel-lisse", "sk-prop-stalk", "sk-thm-inversion"]
lean = ["AlgebraicGeometry.WeilComplex.IsCurvePerverseUpper", "AlgebraicGeometry.WeilComplex.IsCurvePerverseLower", "AlgebraicGeometry.WeilComplex.IsCurvePerverse", "AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff"]
+++
*Proposition (sketch).*

The transform $\DLAFT_\psi$ is an exact equivalence of the perverse
categories of the two affine lines. On a smooth curve these categories
are constructed from ordinary cohomology: the upper class has
$\mathcal H^aK=0$ for $a>0$ and $\mathcal H^0K$ of finite support;
the lower class has $\mathcal H^aK=0$ for $a<-1$ and
$\mathcal H^{-1}K$ with no nonzero finite-support subsheaf.

## Proof

The maximal finite-support subsheaf of an ordinary constructible sheaf,
together with ordinary truncation, constructs the two truncation classes.
Orthogonality follows because a map from a finite-support sheaf to a
sheaf with no such subsheaf is zero.

For an ordinary sheaf $L$, the Fourier stalk formula and curve
cohomological dimension bound the ordinary degrees of
$\DLAFT_\psi(L[1])$ above by zero. Its degree-zero stalk at $a$ is
$H_c^2(A,L\otimes\mathcal L_{\psi(ax)})$. By the coinvariant description,
this can be nonzero only when the generic representation has
$\mathcal L_{\psi(-ax)}$ as a one-dimensional quotient. Distinct $a$
give distinct characters, and at most $\operatorname{rank}L$ distinct
characters can be quotients: the corresponding quotient functionals
are linearly independent. Thus degree zero has finite support.
A finite-support sheaf transforms into a lisse sheaf shifted by one.
Ordinary truncation now shows that Fourier preserves the upper class.
The inverse $\DLAFT_{\psi^{-1}}(1)$ preserves it for the same reason;
orthogonality then gives preservation of the lower class and exactness
on the hearts.

Uses: [sk-d-dl-a1-setup], [sk-l-dl-a1-endpoints], [sk-prop-stalk], [sk-thm-inversion]
