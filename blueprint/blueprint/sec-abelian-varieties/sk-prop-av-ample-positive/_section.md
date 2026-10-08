+++
id = "sk-prop-av-ample-positive"
kind = "section"
title = "Ample modules on proper curves have positive degree"
lean = ["AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple"]
order = 549
uses = ["sk-def-av-ample-degree"]
+++
*Proposition (sketch).*

Let $k$ be algebraically closed, $C$ a proper curve over $k$ of
dimension one (possibly disconnected) and $\cL$ an ample invertible
$\cO_C$-module. Then $\deg\cL>0$.

## Proof

On a proper curve an ample invertible module has positive degree, the
degree being the coefficient of $m$ in the Hilbert polynomial
$m\mapsto\chi(C,\cL^{\otimes m})$, which for $\dim C=1$ is the Hilbert
degree $1!\cdot(\text{leading coefficient})$ of
[sk-def-av-ample-degree]; for disconnected $C$, $\chi$ is additive
over the connected components, each zero-dimensional one contributes a
constant and each one-dimensional one a positive coefficient of $m$.
Dimension one is needed, and the coefficient of $m$ must be
distinguished from the dimension-dependent Hilbert degree: for
$C=\Spec k$ every invertible module is trivial and
$\chi(\cL^{\otimes m})=1$, so the coefficient of $m$ is $0$, while the
Hilbert degree of [sk-def-av-ample-degree] (with $g=0$) is
$0!\cdot1=1$. The statement concerns the coefficient of $m$, i.e. the
Hilbert degree in dimension one.

Uses: [sk-def-av-ample-degree]
