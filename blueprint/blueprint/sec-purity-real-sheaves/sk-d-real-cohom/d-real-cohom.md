+++
id = "d-real-cohom"
kind = "definition"
title = "Cohomology and the Euler series"
order = 2603
uses = ["d-real-setup", "def-weil-weil-sheaf-complex", "def-wf-constant-weil-twist", "def-wf-iota-real"]
+++
For any abelian sheaf $A$ on the etale site, ordinary cohomology means
$H^i(C,A)=R^i\Gamma(C,A)$, computed by an injective resolution.
For a constructible Weil sheaf $\mathcal K$ of
[def-weil-weil-sheaf-complex] on a
curve in the sense of [d-real-setup], $H^i(C,\mathcal K)$ and $H_c^i(C,\mathcal K)$
are the etale cohomology groups obtained from derived global sections
and derived sections with proper support. With an adic lattice, take
the derived inverse limit of its finite coefficient levels and then
invert $\ell$; extend the finite coefficient field as needed.
They carry geometric Frobenius $F$ in the convention of [d-real-setup],
with Tate twists the constant Weil twists of [def-wf-constant-weil-twist].
Using the local characteristic factors $P_x$ of [def-wf-iota-real], the
Euler series is
the locally finite formal product

$$
L_\iota(C_0,\mathcal K,T)
=\prod_{x\in|C_0|}\iota P_x(\mathcal K,T^{e_x})^{-1}
\in 1+T\mathbf C[[T]].
$$

Locally finite means that only finitely many factors contribute to any
fixed coefficient; there are finitely many closed points of bounded degree.

Uses: [d-real-setup], [def-weil-weil-sheaf-complex], [def-wf-constant-weil-twist], [def-wf-iota-real]
