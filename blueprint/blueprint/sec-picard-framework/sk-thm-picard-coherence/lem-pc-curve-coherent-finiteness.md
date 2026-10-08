+++
id = "lem-pc-curve-coherent-finiteness"
kind = "lemma"
title = "Coherent cohomology of a smooth projective curve over an algebraically closed field"
order = 658
uses = ["def-pc-smooth-projective-curve", "lem-pc-projective-curve-finite-projection", "lem-sc-p1-coherent-finite", "lem-sc-p1-hi-vanishing", "pqf-def-coherent", "pqf-lem-affine-vanishing", "pqf-lem-coherent-ft-locnoeth", "pqf-lem-leray"]
+++
Let $k$ be an algebraically closed field, let
$X$ be a smooth projective curve
over $k$, and let $\mathcal F$ be a coherent $\mathcal O_X$-module.
Then $H^i(X,\mathcal F)$ is a finite-dimensional $k$-vector space for
$i=0,1$, and vanishes for $i\ge2$.

## Proof

By [lem-pc-projective-curve-finite-projection], choose a finite
morphism $u:X\to\mathbf P^1_k$. If
$W=\operatorname{Spec}(R)\subset\mathbf P^1_k$ is affine, then
$u^{-1}(W)=\operatorname{Spec}(B)$ with $B$ finite over $R$.
The restriction of $\mathcal F$ is $\widetilde M$ for a finite
$B$-module $M$: this is the affine characterization of coherence on
the locally Noetherian scheme $X$ in
[pqf-lem-coherent-ft-locnoeth]. Hence $M$ is finite over $R$,
so $u_*\mathcal F|_W=\widetilde M$ is coherent. (The same finite
module calculation on principal opens gives the restriction maps;
thus no finite-type-over-$R$ module is being mistaken for a finite
$R$-module.)

For every affine $W\subset\mathbf P^1_k$, its inverse image is affine;
therefore higher cohomology of $\mathcal F$ on $u^{-1}(W)$ vanishes by
[pqf-lem-affine-vanishing]. The Leray spectral sequence of $u$
from [pqf-lem-leray]
then has $R^q u_*\mathcal F=0$ for $q>0$ and gives canonical
isomorphisms

$$
H^i(X,\mathcal F)\cong H^i(\mathbf P^1_k,u_*\mathcal F).
$$

The right side is finite-dimensional for $i=0,1$ by
[lem-sc-p1-coherent-finite], and is zero for $i\ge2$ by
[lem-sc-p1-hi-vanishing]. This proves all assertions.
