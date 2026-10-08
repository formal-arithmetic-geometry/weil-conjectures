+++
id = "lem-fd-l2-plancherel-shift"
kind = "lemma"
title = "The $L^2$-weight shifts by one under the Fourier transform"
order = 2778
uses = ["cor-fd-plancherel", "def-wf-l2-norm"]
+++
Let $\mathcal F$ be a Weil complex on $\mathbf A^1_{k_0}$ and let
$\mathcal G=\operatorname{FT}_\psi(\mathcal F)$. Then, in the
$L^2$-weight parameter $\|\cdot\|$ of
[def-wf-l2-norm],

$$
\|\mathcal G\|\;=\;\|\mathcal F\|+1.
$$

## Proof

By the Plancherel identity of [cor-fd-plancherel] the sums of
squares of the trace functions satisfy

$$
\|f_{\mathcal G}\|_m^2=q^m\|f_{\mathcal F}\|_m^2
$$

for every $m$; substituting into the defining ratio of
[def-wf-l2-norm] shows that the limit superior is positive for a
parameter $\beta$ exactly when it is positive for
$\beta-1$: the two $L^2$-weights satisfy
$\|\mathcal G\|=\|\mathcal F\|+1$.
