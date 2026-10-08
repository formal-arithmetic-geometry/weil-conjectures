+++
id = "def-weil-pbc-property"
kind = "definition"
title = "Proper base-change property"
order = 1048
lean = ["AlgebraicGeometry.Etale.IsBaseChangeIso"]
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions"]
+++
For a proper morphism $f:X\to Y$, define $\mathsf{PBC}(f)$ to mean that for
every morphism $g:Y'\to Y$, every associated Cartesian square $\square$, and
every torsion sheaf $F$ on $X_{\mathrm{et}}$, the map
$\operatorname{Ex}_{\square,F}$ is an isomorphism in the derived category.
The assertion includes the specified map of Definition
[def-weil-pbc-derived-exchange], not an unnamed isomorphism.

## Detailed form

For a proper morphism [def-weil-pbc-scheme-conventions] $f:X\to Y$, write
$\mathrm{PBC}(f)$ if, for every morphism $g:Y'\to Y$, every associated
cartesian square [def-weil-pbc-cartesian-square] $\square$, and
every torsion sheaf [def-weil-pbc-etale-sheaves] $F\in\Ab(X_{\Et})$, the
specified map

$$
 \Ex_{\square,F}:g^{-1}Rf_*F\longrightarrow Rf'_*g'^{-1}F
$$

of the derived exchange morphism [def-weil-pbc-derived-exchange] is
an isomorphism in $\Dplus(Y'_{\Et})$. Here *torsion* means that the
canonical map $\varinjlim_nF[n]\to F$, $F[n]=\ker(n:F\to F)$, is an
isomorphism, equivalently that every geometric stalk $F_{\bar x}$ is a
torsion group (each local section is, locally on $X_{\Et}$, killed by a
positive integer); it is not required that every group $F(U)$ be torsion.
