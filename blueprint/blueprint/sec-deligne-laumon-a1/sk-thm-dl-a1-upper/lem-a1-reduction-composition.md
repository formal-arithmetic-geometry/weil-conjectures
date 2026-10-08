+++
id = "lem-a1-reduction-composition"
kind = "lemma"
title = "Cohomology transport under the finite-map reduction"
order = 2798
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "lem-a1-finite-map-cohomology", "lemma-weil-pbc-finite-direct-image-exact", "prop-functor-package"]
+++
Let $C_0$ be a smooth geometrically connected affine curve, let
$C'_0$ be a smooth geometrically connected curve containing $C_0$
as a dense open with finite complement, let
$g:C'_0\to\mathbf A^1_{k_0}$ be a finite generically etale morphism,
let $j:C_0\hookrightarrow C'_0$, and let $\mathcal F$ be lisse and
punctually $\iota$-pure of weight $w$ on $C_0$. Put
$\mathcal K:=g_*j_!\mathcal F$, a constructible $\Qlb$-Weil sheaf on
$\mathbf A^1_{k_0}$. Then

$$
R\Gamma_c(C,\mathcal F)\simeq R\Gamma_c(\mathbf A^1,\mathcal K),
\qquad\text{hence}\qquad
H_c^i(C,\mathcal F)\simeq H_c^i(\mathbf A^1,\mathcal K)\quad(i\in\mathbf Z).
$$

## Proof

By the finite-map transport applied to the sheaf $j_!\mathcal F$
on $C'_0$: the finite morphism $g$ is proper and $g_*$ is exact
(the finite-direct-image exactness
[lemma-weil-pbc-finite-direct-image-exact]), so

$$
R\Gamma_c(C,\mathcal F)=R\Gamma_c\bigl(C'_0,j_!\mathcal F\bigr)
\simeq R\Gamma_c\bigl(\mathbf A^1_{k_0},g_*j_!\mathcal F\bigr)
=R\Gamma_c(\mathbf A^1,\mathcal K),
$$

with the same compact-support composition of [prop-functor-package]
as in [lem-a1-finite-map-cohomology].
