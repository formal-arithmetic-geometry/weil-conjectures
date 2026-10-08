+++
id = "sk-def-pbc"
kind = "section"
title = "The PBC property"
order = 1047
lean = ["AlgebraicGeometry.Etale.HasTorsionBaseChange"]
uses = ["sk-def-conv", "sk-def-exchange"]
+++
*Definition (sketch).*

For a proper morphism $f:X\to Y$, write
$\mathrm{PBC}(f)$ if the exchange morphism
$\Ex_{\square,F}$ is an isomorphism in $\Dplus$ for every base
change and every torsion sheaf $F$ on $X_{\Et}$. Here a sheaf of
abelian groups $F$ on $X_{\Et}$ is *torsion* if the canonical
map $\varinjlim_nF[n]\to F$, $F[n]=\ker(n:F\to F)$, is an
isomorphism (equivalently, every stalk $F_{\bar x}$ at a geometric
point is a torsion group, i.e. every local section is, locally,
killed by a positive integer); this is weaker than asking that
each group $F(U)$ be torsion.

Uses: [sk-def-conv], [sk-def-exchange]
