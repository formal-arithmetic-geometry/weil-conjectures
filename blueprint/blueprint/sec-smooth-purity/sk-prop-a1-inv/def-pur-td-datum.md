+++
id = "def-pur-td-datum"
kind = "definition"
title = "Trace–diagonal datum"
order = 1955
uses = ["def-pur-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-weil-derived-tensor-functorial"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be separated finite type; Put
$W=X\times_YX$ with projections $p_1,p_2$ and
diagonal $\Delta$, and let $L\in D^b_{ctf}(X,\Lambda)$ be
tensor-invertible. A *trace–diagonal datum* for $(f,L)$ is a
pair

$$
\operatorname{tr}_f:Rf_!L\longrightarrow\Lambda_Y,
\qquad
\operatorname{cl}_\Delta:\Delta_!\Lambda_X\longrightarrow p_2^*L.
$$

The *induced functor* (a functor by [lem-weil-derived-tensor-functorial]) is

$$
G_L:D^b_{ctf}(Y,\Lambda)\longrightarrow D^b_{ctf}(X,\Lambda),
\qquad G_L(K)=Lf^*K\otimes^L_{\Lambda_X}L,
$$

and $\operatorname{tr}_f$ defines, via the projection formula, the
*counit*

$$
\epsilon_K:Rf_!G_L(K)\cong K\otimes^L_{\Lambda_Y}Rf_!L
\xrightarrow{\ \operatorname{id}\otimes\operatorname{tr}_f\ }K;
$$

$\operatorname{cl}_\Delta$ defines, the *unit*

$$
\eta_A:A\cong Rp_{2!}\bigl(p_1^*A\otimes^L_{\Lambda_W}\Delta_!\Lambda_X\bigr)
\xrightarrow{\ \operatorname{id}\otimes\operatorname{cl}_\Delta\ }
Rp_{2!}\bigl(p_1^*A\otimes^L_{\Lambda_W}p_2^*L\bigr)
\cong G_L(Rf_!A).
$$

The two *triangular composites* are the composites

$$
Rf_!A\xrightarrow{\ Rf_!\eta_A\ }Rf_!G_LRf_!A
\xrightarrow{\ \epsilon_{Rf_!A}\ }Rf_!A
$$

and

$$
G_LK\xrightarrow{\ \eta_{G_LK}\ }G_LRf_!G_LK
\xrightarrow{\ G_L\epsilon_K\ }G_LK,
$$

natural in $A\in D^b_{ctf}(X,\Lambda)$ and
$K\in D^b_{ctf}(Y,\Lambda)$.
