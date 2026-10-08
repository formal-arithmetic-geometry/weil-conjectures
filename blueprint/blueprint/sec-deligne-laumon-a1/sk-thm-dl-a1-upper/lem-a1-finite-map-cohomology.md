+++
id = "lem-a1-finite-map-cohomology"
kind = "lemma"
title = "Cohomology under a finite curve map"
order = 2796
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-finite-direct-image-exact", "prop-functor-package"]
+++
For a finite map $g:C_0\to\mathbf A^1_{k_0}$ of separated finite-type
$k_0$-schemes and a lisse Weil sheaf $\mathcal F$ on $C_0$,

$$
H_c^i(C,\mathcal F)\simeq H_c^i(\mathbf A^1,g_*\mathcal F)
$$

for every $i$.

## Proof

A finite morphism is proper, so $Rg_!=Rg_*$ by the properness law of
[prop-functor-package], and $g_*$ is exact by the finite-direct-
image exactness [lemma-weil-pbc-finite-direct-image-exact]: hence

$$
R\Gamma_c(C,\mathcal F)=Ra_{!}Rg_!\mathcal F\simeq Ra_{!}g_*\mathcal F
=R\Gamma_c(\mathbf A^1,g_*\mathcal F)
$$

(the compact-support composition of [prop-functor-package]), and
taking cohomology gives the displayed identification degreewise.
