+++
id = "lemma-nagata-conrad-strict-transform-in-charts"
kind = "lemma"
title = "Strict transforms live in the charts of the other centre (Deligne, *Lemme* 0.2) (Conrad)"
order = 206
uses = ["def-nagata-blowup-chart-ring", "def-nagata-strict-transform", "lemma-nagata-strict-transform-chart-closed", "prop-nagata-affine-blowup-chart-cover"]
+++
**Status.** Bypassed by the formalized route: Deligne's disjointness blow-up
is formalized as the single statement
`AlgebraicGeometry.disjoint_closure_range_of_blowupMap_sup`,
which absorbs this step.

Let $X$ be a scheme and let $Y,Y'\subseteq X$ be closed subschemes with
quasi-coherent ideals $\mathcal I_Y,\mathcal I_{Y'}$. In
$\widetilde X=\operatorname{Bl}_{\mathcal I_Y+\mathcal I_{Y'}}(X)$ the strict
transform $\widetilde Y$ of $Y$ is contained in the union of the charts
$U(s)$, taken over all local sections $s$ of $\mathcal I_{Y'}$ on all affine
opens of $X$.

Consequently, if $Y_1,\ldots,Y_n$ are closed subschemes of $X$ and
$\widetilde X=\operatorname{Bl}_{\sum_j\mathcal I_{Y_j}}(X)$, then the strict
transforms satisfy $\bigcap_j\widetilde Y_j=\varnothing$.

## Proof

Both assertions are local on $X$, so let $X=\operatorname{Spec}(A)$ and put
$I=\Gamma(X,\mathcal I_Y)$ and $J=\Gamma(X,\mathcal I_{Y'})$. The charts
$U(s)$ for $s\in I\cup J$ cover $\widetilde X$ by
[prop-nagata-affine-blowup-chart-cover], since such elements generate
$I+J$. It therefore suffices to prove that $U(s)$ is disjoint from
$\widetilde Y$ for every $s\in I$. On the chart $U(s)$ the strict transform
of $Y=V(I)$ is cut out by the saturation of $I\cdot A[(I+J)/s]$ with respect
to $s$, that is, by

$$
I_s\cap A[(I+J)/s]
$$

formed inside $A_s$
([lemma-nagata-strict-transform-chart-closed]). Because $s\in I$ the
element $1=s/s$ lies in that ideal, so the ideal is the unit ideal and the
overlap of $U(s)$ with $\widetilde Y$ is empty.

For the second assertion put $I_j=\Gamma(X,\mathcal I_{Y_j})$. The centre
is $\sum_jI_j$, so the charts $U(s)$ for $s\in\bigcup_jI_j$ cover
$\widetilde X$. Fix such an $s$, say $s\in I_1$. The computation just made,
with $I=I_1$ and $J=I_2+\cdots+I_n$, shows $U(s)\cap\widetilde Y_1 =\varnothing$. Hence every point of $\widetilde X$ misses at least one
$\widetilde Y_j$, and the intersection of all of them is empty.
