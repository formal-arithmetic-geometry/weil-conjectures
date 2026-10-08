+++
id = "prop-a1-curve-boundary-sequence"
kind = "theorem"
title = "Boundary localization triangle for a curve"
order = 2726
tags = ["latex:proposition"]
uses = ["def-weil-open-closed-recollement", "def-weil-ordinary-compact-cohomology", "def-wf-middle-extension", "lem-a1-finite-boundary-cohomology", "lem-fin-boundary-sheaf", "prop-sf-open-closed-triangle-all-stages"]
+++
Let $j:U_0\hookrightarrow C_0$ be a dense open immersion of smooth
curves, let $i:Z_0=C_0\setminus U_0\hookrightarrow C_0$, and let
$\mathcal F$ be lisse on $U_0$. The open–closed localization
triangle, with the middle extension of [def-wf-middle-extension],
gives

$$
R\Gamma_c(U,\mathcal F)\longrightarrow
R\Gamma_c(C,j_*\mathcal F)\longrightarrow
R\Gamma_c(Z,i^*j_*\mathcal F)\longrightarrow\ .
$$

In particular, because the finite-boundary term is concentrated in
degree zero, the degree-one segment is

$$
H_c^0(Z,i^*j_*\mathcal F)\longrightarrow H_c^1(U,\mathcal F)
\longrightarrow H_c^1(C,j_*\mathcal F)\longrightarrow0
$$

and the degree-zero injection
$H_c^0(U,\mathcal F)\hookrightarrow H_c^0(C,j_*\mathcal F)$.

## Proof

The boundary triangle $j_!\mathcal F\to j_*\mathcal F\to i_*i^*j_*\mathcal F\to$ (whose boundary term is supported on the finite closed subscheme $Z$) is the open–closed recollement triangle of [def-weil-open-closed-recollement] of the framework chapter, which exists for Qlb-Weil complexes by [prop-sf-open-closed-triangle-all-stages], applied to $K=j_*\mathcal F$, with the extension-by-zero and derived-direct-image conventions of that definition. The last term
$R\Gamma_c(Z,i^*j_*\mathcal F)$ is concentrated in degree zero by the
finite-boundary computation [lem-a1-finite-boundary-cohomology]
(applicable since $i^*j_*\mathcal F$ is constructible by [lem-fin-boundary-sheaf]),
so the long exact cohomology sequence of the triangle gives the
displayed degree-one segment and the stated injections.
