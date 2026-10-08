+++
id = "sk-thm-product"
kind = "section"
title = "Supported product over a relative base"
order = 2436
uses = ["sk-def-ops", "sk-thm-sf-kunneth-relative"]
+++
*Theorem (sketch).*

In the setting of [sk-def-set], let $B$ be a finite-type $k$-scheme,
$f:X\to B$, $g:Y\to B$ separated of finite type,
$h=f\times_Bg:X\times_BY\to B$ with projections $p,q$, and
$K\boxtimes L=p^*K\otimes^L_\Lambda q^*L$. For closed immersions
$i:Z\hookrightarrow X$, $j:W\hookrightarrow Y$, with
$i\times_Bj:Z\times_BW\hookrightarrow X\times_BY$,

$$
Rf_!\bigl(i_*i^*K\bigr)\otimes^L_{\Lambda_B}Rg_!\bigl(j_*j^*L\bigr)\cong
Rh_!\bigl((i\times_Bj)_*(i\times_Bj)^*(K\boxtimes L)\bigr).
$$

For $B=\Spec k$ this reads
$R\Gamma_c(Z,i^*K)\otimes^L_\Lambda R\Gamma_c(W,j^*L)\cong R\Gamma_c\bigl(Z\times W,(K\boxtimes L)|_{Z\times W}\bigr)$.
(Blueprint 13, thm:sf-kunneth-relative.)
*Note: this theorem seems never to be used later — relative products
are taken directly from [sk-thm-sf-kunneth-relative], of which this is the
case of $i_*i^*K$ and $j_*j^*L$, and the supports Künneth needed by purity is
proved there directly — so it has no detailed counterpart in the
blueprint.*

## Proof

Apply the relative compact-support product of
[sk-thm-sf-kunneth-relative] to $i_*i^*K$ and $j_*j^*L$, using that
the exterior product of extensions by zero along closed immersions is the
extension by zero of the exterior product:
$(i_*i^*K)\boxtimes(j_*j^*L)\cong(i\times_Bj)_*(i\times_Bj)^*(K\boxtimes L)$.
For $B=\Spec k$, apply $\Fib_s$ of [sk-def-ops]; since $i$ and $j$
are proper, $Ra_{X!}i_*=Ra_{Z!}$ and $Ra_{Y!}j_*=Ra_{W!}$.

Uses: [sk-def-ops], [sk-thm-sf-kunneth-relative]
