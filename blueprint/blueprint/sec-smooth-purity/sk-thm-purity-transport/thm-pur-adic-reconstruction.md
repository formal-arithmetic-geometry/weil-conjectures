+++
id = "thm-pur-adic-reconstruction"
kind = "theorem"
title = "Adic reconstruction"
order = 2023
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-complete-integral-detailed", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-weil-pbc-reconstruction-uniform-tower", "thm-pur-finite-coefficient-smooth-purity", "thm-pur-finite-reduction-of-purity"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$f:X\to Y$ be smooth separated of relative dimension $d$, and let
$K\in D^b_{ctf}(Y,\mathcal O_E)$ with finite reductions
$K_n\in D^b_{ctf}(Y,A_{E,n})$. The comparisons
$\gamma_{f,K_n}$ of [thm-pur-finite-coefficient-smooth-purity] form a
morphism of normalized systems in the sense of
[def-weil-pbc-adic-coefficient-datum], and they induce an isomorphism

$$
Lf^*K(d)[2d]\xrightarrow{\ \sim\ }Rf^!K
$$

in $D^b_{ctf}(X,\mathcal O_E)$, whose reduction at every level $n$ is
exactly $\gamma_{f,K_n}$.

## Proof

By [thm-pur-finite-reduction-of-purity], the reduction of
$\gamma_{f,K_{n+1}}$ along $A_{E,n+1}\to A_{E,n}$ is
$\gamma_{f,K_n}$, i.e. the comparisons are compatible with the
transition maps of the normalized system; the common bounds and
stratifications of [def-weil-pbc-bounded-constructible-tower] are those
of $K$ with the same $d$-shift. Hence
$(\gamma_{f,K_n})_{n}$ is a morphism of normalized systems, whose
realization under the uniform-tower reconstruction of
[lem-weil-pbc-reconstruction-uniform-tower] is the displayed
isomorphism over $\mathcal O_E$, and the levelwise nature of the
reconstruction gives the compatibility with the reductions.
