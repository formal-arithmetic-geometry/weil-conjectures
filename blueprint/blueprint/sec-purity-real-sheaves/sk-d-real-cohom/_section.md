+++
id = "sk-d-real-cohom"
kind = "section"
title = "Cohomology and the Euler series"
order = 2602
uses = ["sec-smooth-purity", "sk-d-real-operations", "sk-d-real-setup", "sk-d-real-weights", "sk-d-real-weil"]
lean = ["AlgebraicGeometry.WeilGroup.eulerSeries"]
+++
*Definition (sketch).*

For any abelian sheaf $A$ on the etale site, ordinary cohomology means
$H^i(C,A)=R^i\Gamma(C,A)$, computed by an injective resolution.
For a constructible Weil sheaf $\mathcal K$ on a
curve, $H^i(C,\mathcal K)$ and $H_c^i(C,\mathcal K)$
are the etale cohomology groups obtained from derived global sections
and derived sections with proper support. With an adic lattice, take
the derived inverse limit of its finite coefficient levels and then
invert $\ell$; extend the finite coefficient field as needed.
They carry geometric Frobenius $F$, with the
Tate convention fixed above.
Using the local polynomials, the Euler series is
the locally finite formal product

$$
L_\iota(C_0,\mathcal K,T)
=\prod_{x\in|C_0|}\iota P_x(\mathcal K,T^{e_x})^{-1}
\in 1+T\mathbf C[[T]].
$$

Locally finite means that only finitely many factors contribute to any
fixed coefficient; there are finitely many closed points of bounded degree.

Uses: [sk-d-real-operations], [sk-d-real-setup], [sk-d-real-weights], [sk-d-real-weil]
