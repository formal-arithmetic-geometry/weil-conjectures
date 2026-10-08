+++
id = "sk-thm-iff"
kind = "section"
title = "PBC $\\Leftrightarrow$ IA"
order = 1067
lean = ["AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity"]
uses = ["sk-def-conv", "sk-def-exchange", "sk-def-ia", "sk-def-pbc", "sk-thm-acyclicity"]
+++
*Theorem (sketch).*

For a proper morphism $f$:
$\mathrm{PBC}(f)$ in the sense of [sk-def-pbc] holds if and only if
$\mathrm{IA}(f)$ in the sense of [sk-def-ia] holds.

## Proof

$\Rightarrow$ is immediate: $Rf_*I=f_*I$ for $I$ injective, so the
$\mathrm{IA}_r$ vanishings of [sk-def-ia] follow from
$\mathrm{PBC}$. $\Leftarrow$: take an injective resolution
$E\to I^\bullet$ of an $\Fq$-sheaf $E$; [sk-def-ia] says every
$g'^{-1}I^m$ is $f'_*$-acyclic, so by the criterion of
[sk-thm-acyclicity] the complex $f'_*g'^{-1}I^\bullet$ computes
$Rf'_*g'^{-1}E$, while $g^{-1}$ exact makes $g^{-1}f_*I^\bullet$
compute $g^{-1}Rf_*E$. The two complexes are linked termwise by the
*underived* exchange of [sk-def-exchange], which is an
isomorphism in every degree — and here is the only non-formal step:
at a geometric point of $Y'$, both stalks compute sections over the
same closed geometric fibre $X_{\bar s}=X'_{\bar t}$, by the
degree-zero comparison $\Gamma(Z,\cdot)\cong\Gamma(Z_s,\cdot)$ for
$Z$ proper over a strictly henselian base (Stein's connectedness +
restriction on spectral spaces, checked stalkwise, and geometric
stalks are conservative). Prime coefficients give all $n$-torsion
sheaves by the exact sequence $0\to F[r]\to F\to rF\to0$ and the
five lemma; all torsion sheaves are filtered unions $F=\varinjlim F[n]$, over which the proper $R^qf_*$ commutes.

Uses: [sk-def-conv], [sk-def-exchange], [sk-def-ia], [sk-def-pbc], [sk-thm-acyclicity]
