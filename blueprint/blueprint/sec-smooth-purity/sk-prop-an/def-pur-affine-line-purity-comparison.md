+++
id = "def-pur-affine-line-purity-comparison"
kind = "definition"
title = "Affine-line purity comparison"
order = 1974
uses = ["def-amb-p1-trace", "def-coefficient-twists-detailed", "def-exchange-projection", "def-pur-affine-line-datum", "def-pur-conventions", "def-weil-exceptional-inverse-image"]
+++
In the finite-coefficient purity conventions,
let $p:\mathbf A^1_Y\to Y$ be the projection and
$j:\mathbf A^1_Y\hookrightarrow\mathbf P^1_Y$, $q:\mathbf P^1_Y\to Y$
its standard compactification, as in
the affine-line datum.
Define integration by restriction of the already constructed
projective-line trace:

$$
\int_p:Rp_!\Lambda(1)[2]=Rq_*j_!\Lambda(1)[2]
\longrightarrow Rq_*\Lambda(1)[2]
\xrightarrow{t_q}\Lambda_Y.
$$

For $K\in D^b_{ctf}(Y,\Lambda)$, define $\gamma_{p,K}$ to be the
exceptional adjoint of

$$
Rp_!Lp^*K(1)[2]
\xrightarrow{\sim}K\otimes^L Rp_!\Lambda(1)[2]
\xrightarrow{1_K\otimes\int_p}K,
$$

using the compact-support projection map
and Tate twists.
Thus $\gamma_{p,K}:Lp^*K(1)[2]\to Rp^!K$ is defined in the ambient
category; its isomorphy and bounded constructibility are conclusions.
