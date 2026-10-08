+++
id = "def-sf-kv-maps"
kind = "definition"
title = "The product comparison maps"
order = 2223
uses = ["def-compact-support-direct-image-detailed", "def-sf-datum", "def-sf-pf", "def-trf-admissibility", "def-weil-exceptional-inverse-image", "def-weil-integral-rational-qbar-compact-support", "thm-sf-kunneth-relative"]
+++
For $i=1,2$ let $f_i:X_i\to Y_i$ be separated of finite type between
finite-type $k$-schemes, exceptionally admissible in the sense of
[def-trf-admissibility] where $Rf^!$ occurs — which every such morphism is,
no ambient datum being assumed — (with $Rf^!$ the exceptional
inverse image of [def-weil-exceptional-inverse-image] and $Rf_!$ the
compact-support direct image of [def-compact-support-direct-image-detailed],
[def-weil-integral-rational-qbar-compact-support]), put $f=f_1\times f_2$, and let
$L_i\in\Dctf(Y_i,\Lambda)$, $B_i\in\Dctf(X_i,\Lambda)$.

3pt
1. **(i)** The $!$-Künneth
$\mathrm{Ku}_!:Rf_!(B_1\boxtimes B_2)\xrightarrow{\ \sim\ } Rf_{1!}B_1\boxtimes Rf_{2!}B_2$ is [thm-sf-kunneth-relative] for the base
$B=Y_1\times Y_2$, using
$X_1\times X_2=(X_1\times Y_2)\times_B(Y_1\times X_2)$. It is an isomorphism.
1. **(ii)** The *exceptional Künneth*
$\alpha:Rf_1^!L_1\boxtimes Rf_2^!L_2\to Rf^!(L_1\boxtimes L_2)$ is the
exceptional adjoint of
$$
Rf_!\bigl(Rf_1^!L_1\boxtimes Rf_2^!L_2\bigr)
\xrightarrow{\ \mathrm{Ku}_!\ }
Rf_{1!}Rf_1^!L_1\boxtimes Rf_{2!}Rf_2^!L_2
\xrightarrow{\ \varepsilon_1\boxtimes\varepsilon_2\ }
L_1\boxtimes L_2 ,
$$
where the $\varepsilon_i$ are the counits of $Rf_{i!}\dashv Rf_i^!$
(axiom (A1) of [def-sf-datum]).
1. **(iii)** For $E_i\in\Dctf(Y_i,\Lambda)$, on the same scheme $Y_i$ as
$L_i$, the *external Hom* map
$$
\beta:\RHom(E_1,L_1)\boxtimes\RHom(E_2,L_2)
\longrightarrow\RHom\bigl(E_1\boxtimes E_2,L_1\boxtimes L_2\bigr)
$$
is the tensor–Hom transpose of the two evaluations, with the tensor symmetry
and its Koszul signs.
1. **(iv)** For separated finite-type $k$-schemes $X,Y$ whose structure
morphism $a_Y$ and product projection
$p_X=\operatorname{id}_X\times a_Y:X\times Y\to X$ satisfy the
exceptional-adjoint admissibility of [def-trf-admissibility] (the inputs
for $\omega_Y$ and $\mathbb D_Y$, for $Rp_X^!$, and for
$\alpha_{\operatorname{id}_X,a_Y}$), for
$M\in\Dctf(X,\Lambda)$ and $N\in\Dctf(Y,\Lambda)$, with
$p_X,p_Y$ the projections of $X\times Y$, and with the Verdier dual
$\mathbb D_Y$ and dualizing complex $\omega_Y=Ra_Y^!\Lambda$ of [def-sf-pf], the
*Künneth–Verdier* map is
$$
\begin{aligned}
\kappa_{M,N}:M\boxtimes\mathbb D_YN
&\xrightarrow{\ \beta\ }\RHom\bigl(p_Y^*N,M\boxtimes\omega_Y\bigr)\\
&\xrightarrow{\ \RHom(1,\alpha_{\operatorname{id}_X,a_Y})\ }
\RHom\bigl(p_Y^*N,Rp_X^!M\bigr),
\end{aligned}
$$
using the unit identifications $\RHom(\Lambda_X,M)=M$ and
$\Lambda_X\boxtimes N=p_Y^*N$; here $\beta$ is applied to the pairs
$(E_1,L_1)=(\Lambda_X,M)$ on $X$ and $(E_2,L_2)=(N,\omega_Y)$ on $Y$.

Only $\mathrm{Ku}_!$ is built from isomorphisms; invertibility of
$\alpha,\beta,\kappa$ is the content of [prop-trf-exceptional-kunneth], [prop-trf-external-hom]
and [thm-trf-kunneth-verdier].

Uses: [def-compact-support-direct-image-detailed], [def-sf-datum], [def-sf-pf], [def-trf-admissibility], [def-weil-exceptional-inverse-image], [def-weil-integral-rational-qbar-compact-support], [thm-sf-kunneth-relative]
