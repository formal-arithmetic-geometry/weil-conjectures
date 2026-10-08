+++
id = "lem-a1-reduction-lisse-pure"
kind = "lemma"
title = "Lisse purity of the transported complex"
order = 2799
uses = ["def-weil-punctual-weights", "lem-a1-finite-map-purity"]
+++
Let $C_0$ be a smooth geometrically connected affine curve, let
$C'_0$ be a smooth geometrically connected curve containing $C_0$
as a dense open with finite complement, let
$g:C'_0\to\mathbf A^1_{k_0}$ be a finite generically etale morphism,
let $j:C_0\hookrightarrow C'_0$, and let $\mathcal F$ be lisse and
punctually $\iota$-pure of weight $w$ on $C_0$. Put
$\mathcal K:=g_*j_!\mathcal F$ and let $B$ be the branch locus of
$g$. Then the restriction $\mathcal K|_W$ to
$W:=\mathbf A^1_{k_0}\setminus(B\cup g(C'_0\setminus C_0))$
is lisse and punctually $\iota$-pure of weight $w$.

## Proof

On the open
$W:=\mathbf A^1_{k_0}\setminus(B\cup g(C'_0\setminus C_0))$
the morphism $g$ is finite etale, all of its inverse image lies
in $C_0$, and
$\mathcal K|_W=g_*(j_!\mathcal F)|_W$ sheaf-theoretically, so the
lissity and the punctual purity of weight $w$ in the sense of
[def-weil-punctual-weights] follow from
[lem-a1-finite-map-purity].
