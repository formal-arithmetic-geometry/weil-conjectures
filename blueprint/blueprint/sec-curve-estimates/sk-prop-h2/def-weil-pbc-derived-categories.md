+++
id = "def-weil-pbc-derived-categories"
kind = "definition"
title = "Derived categories of etale sheaves"
order = 933
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks"]
+++
For a scheme $T$ and a commutative ring $R$, let
$\mathsf{Cpx}(\Mod(T_{\Et},R))$ be the abelian category of cochain complexes
of $R_T$-module sheaves and let

$$
 D(T_{\Et},R)=\mathsf{Cpx}(\Mod(T_{\Et},R))
 [\{\text{quasi-isomorphisms}\}^{-1}]
$$

be its Verdier localization at quasi-isomorphisms; the notation without $R$
refers to sheaves of abelian groups. The triangulated category
$\Dplus(T_{\Et},R)$ is the full subcategory of objects whose cohomology
sheaves vanish below some integer, and $D^b(T_{\Et},R)$ is the full
subcategory of objects with only finitely many nonzero cohomology sheaves.
For $K\in D(T_{\Et},R)$ write $\mathcal H^i(K)$ for its $i$-th cohomology
sheaf (with respect to the standard t-structure). An object has *torsion
cohomology* if every $\mathcal H^i(K)$ is a torsion sheaf
[def-weil-pbc-etale-sheaves].
