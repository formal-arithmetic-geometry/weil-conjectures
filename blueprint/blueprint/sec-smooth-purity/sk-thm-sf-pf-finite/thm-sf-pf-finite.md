+++
id = "thm-sf-pf-finite"
kind = "theorem"
title = "Finite coefficients on the étale site"
order = 1879
uses = ["def-sf-datum", "def-sf-pf", "lem-weil-finite-compact-projection-formula"]
+++
In the setting of [def-sf-datum], let $\Lambda=A_{E,n}$, let
$f:X\to Y$ be separated of finite type, and let $K$ and $L$ be bounded
constructible complexes on the étale sites with $L$ of finite Tor
amplitude. Then $\operatorname{PF}_{f,K,L}$ is an isomorphism, natural in
$K$ and $L$. ([lem-weil-finite-compact-projection-formula]; its proof is complete
and is the base case of the passage to all stages below.)

## Proof

The projection transformation used below is [def-sf-pf], and the
finite compact-support case is
[lem-weil-finite-compact-projection-formula].
Step 1: split off a compactification $f=\bar f\circ j$; then
$Rf_!=R\bar f_*j_!$ and the projection transformation is the composite of
the direct-image projection map for $\bar f$ with the identification
$j_!K\otimes^L\bar f^*L\cong j_!(K\otimes^Lf^*L)$, which is checked on
étale stalks (on the open $X$ both sides have stalk
$K_{\bar x}\otimes L_{\bar x}$, and off $X$ both are zero). Step 2: for a
geometric point $\bar y\to Y$ with fibre $X_{\bar y}$, compact-support base
change identifies the stalk of the projection map with
$R\Gamma_c(X_{\bar y},K^{\mathrm{fib}}_{\bar y})\otimes^L P\to R\Gamma_c(X_{\bar y},K^{\mathrm{fib}}_{\bar y}\otimes^L\underline P)$,
where $P=L_{\bar y}$ and $\underline P$ is the pullback of the complex of
$A_{E,n}$-modules $P$. Step 3: the fibrewise map is an isomorphism for
every $P$: choosing a bounded complex of finite free modules representing
$P$, both sides are exact functors of $P$ agreeing on $P=A_{E,n}$ (the unit
identification), and the class of $P$ for which the map is an isomorphism
is closed under finite sums, shifts, cones and direct summands. Step 4:
all geometric stalks of the cone vanish, and geometric stalks are
conservative on the étale site, so the cone is zero.
