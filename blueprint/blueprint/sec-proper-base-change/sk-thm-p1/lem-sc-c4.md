+++
id = "lem-sc-c4"
kind = "lemma"
title = "C4: finiteness for constructible prime-to-char sheaves"
order = 1115
uses = ["def-sc-curves", "def-weil-pbc-eight-curve-assertions", "def-weil-pbc-etale-sheaves", "lem-sc-affine-open-proper", "lem-sc-affine-unit-quotient", "lem-sc-compactification", "lem-sc-pic-affine", "thm-sc-affine-cohomology", "thm-sc-proper-cohomology"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth separated connected curve over $k$, let
$r$ be prime to $\operatorname{char}k$, and let the constant sheaf
$\mathbf F_r$ be viewed as a
constructible sheaf. Then
$\mathbf F_r$ satisfies $\mathcal C_4(C,\mathbf F_r)$ of
[def-weil-pbc-eight-curve-assertions]: $H^q(C_{\Et},\mathbf F_r)$
is a finite abelian group for every $q\geq0$.

## Proof

The constant sheaf $\mathbf F_r$ is locally constant with finite
stalks on $C$, hence [def-weil-pbc-etale-sheaves]
(constructible). By [lem-sc-compactification] and
[lem-sc-affine-open-proper], $C$ either is proper or is
affine. If $C$ is proper, the cohomology groups are
$\mathbf Z/r\mathbf Z$, $(\mathbf Z/r\mathbf Z)^{2g}$,
$\mathbf Z/r\mathbf Z$ and $0$ by
[thm-sc-proper-cohomology], hence finite. If $C$ is affine,
$H^0(C,\mathbf F_r)=\mathbf Z/r\mathbf Z$ and the higher groups
above degree one vanish by [thm-sc-affine-cohomology]. That
theorem expresses $H^1$ as an extension of the finite group
$\operatorname{Pic}(C)[r]$ of [lem-sc-pic-affine] by the
finite unit quotient of [lem-sc-affine-unit-quotient].
Thus $H^1$ is finite as well.
