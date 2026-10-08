+++
id = "rem-ptr-trf-supported-pairing-1"
kind = "remark"
title = "Pointer to the properties of [def-trf-supported-pairing]"
order = 2312
uses = ["def-trf-correspondence-between-pairs", "def-trf-supported-pairing"]
+++
In the notation of [def-trf-supported-pairing], for an opposite pair
between $(X,K)$ and $(Y,L)$ the recipe has three ingredients: the inverse
Künneth–Verdier maps give the supported classes

$$
\widetilde u:Rc_!A_C\longrightarrow P:=L\boxtimes_A^{\mathrm L}D_XK,
\qquad
\widetilde v:R\bar d_!A_D\longrightarrow Q:=D_YL\boxtimes_A^{\mathrm L}K;
$$

for $e:E(C,D)\to Z$ the map from the fiber product of the two
supports ([def-trf-correspondence-between-pairs]), the projection formula and $!$-base change give
$Re_!A_E\simeq Rc_!A_C\otimes_A^{\mathrm L}R\bar d_!A_D$; and the two
Verdier evaluations followed by
$\omega_Y\boxtimes_A^{\mathrm L}\omega_X\simeq\omega_Z$ contract
$P\otimes_A^{\mathrm L}Q$ to $\omega_Z$. Every identification used is
canonical, so $\langle u,v\rangle_{\mathrm{LV}}$ depends only on the
two correspondences. In the diagonal case
$(Y,L)=(X,K)$, $(D,d,v)=(X,\Delta_X,1_K)$, where $E(C,D)=\Fix(c)$, the
section $\langle u,1_K\rangle_{\mathrm{LV}}$ is the trace class
$\Tr_c(u)$ of [def-trf-trace-class], by
[lem-trf-trace-class-diagonal-pairing].
