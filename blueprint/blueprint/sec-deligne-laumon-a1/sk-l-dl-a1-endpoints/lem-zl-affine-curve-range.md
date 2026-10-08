+++
id = "lem-zl-affine-curve-range"
kind = "lemma"
title = "Cohomological range of an affine curve"
order = 2735
uses = ["def-compact-support-direct-image-detailed", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-qbar-category", "lem-sc-cohomological-dimension", "lem-sc-compactification", "lem-weil-pbc-mittag-leffler", "prop-weil-pbc-direct-image-limits", "sbc-thm-finiteness-finite-type"]
+++
If $C_0$ is a smooth affine curve and $\mathcal F$ is constructible
in the coefficients of [def-weil-pbc-qbar-category], then
$H_c^i(C,\mathcal F)=0$ for $i\notin\{0,1,2\}$.

## Proof

Choose a smooth proper completion $j:C\hookrightarrow\overline C$
by [lem-sc-compactification]. At finite coefficient level,

$$
R\Gamma_c(C,\mathcal F_n)
=R\Gamma(\overline C,j_!\mathcal F_n)
$$

by [def-compact-support-direct-image-detailed]. The object
$j_!\mathcal F_n$ is a sheaf in degree zero.
The cohomological-dimension bound
[lem-sc-cohomological-dimension](a), applied to this sheaf,
therefore gives vanishing outside degrees $0,1,2$.

For a constructible integral lattice and its finite reductions,
the groups $H^r(\overline C,j_!\mathcal F_n)$ are finite by
[sbc-thm-finiteness-finite-type] applied to the proper
structure morphism of $\overline C$.
The inverse-limit computation
[prop-weil-pbc-direct-image-limits] has Milnor exact sequence

$$
0\longrightarrow\varprojlim\nolimits^1
H^{r-1}(\overline C,j_!\mathcal F_n)
\longrightarrow H_c^r(C,\mathcal F_{\mathcal O_E})
\longrightarrow\varprojlim H^r(\overline C,j_!\mathcal F_n)
\longrightarrow0.
$$

The first term vanishes by [lem-weil-pbc-mittag-leffler];
thus passage to the integral lattice introduces no degree $3$
term. Rationalizing, and then making the finite scalar extensions
of [def-weil-pbc-qbar-category], preserves this vanishing and
gives the assertion for $\mathcal F$.
The argument concerns sheaves in degree zero: an arbitrary shift
of such a sheaf would shift the cohomological range.
