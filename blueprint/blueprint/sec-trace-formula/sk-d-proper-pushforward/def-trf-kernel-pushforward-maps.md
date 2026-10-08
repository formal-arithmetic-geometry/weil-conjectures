+++
id = "def-trf-kernel-pushforward-maps"
kind = "definition"
title = "Kernel, evaluation and support maps of a proper pushforward diagram"
order = 2328
uses = ["def-sf-kv-maps", "def-trf-coefficient-pushforward", "def-trf-dualizing-complex", "def-trf-external-product", "def-trf-trace-class-source", "fix-prop-adjunctions", "lem-trf-fixed-map-proper", "lem-trf-trace-map-from-external-duality", "prop-functor-package", "thm-sf-comp-composition", "thm-trf-dualizing-complex-composition", "thm-trf-fixed-point-base-change", "thm-trf-verdier-duality"]
+++
Let $(f,g):(C,c)\to(D,b)$ be a proper pushforward diagram of
[def-trf-coefficient-pushforward], with $K$, $u$, $K'=Rf_*K$,
$F_c,F_b$, $i_c,d_c,i_b,d_b$ and the proper $h:F_c\to F_b$ as there and in
[lem-trf-fixed-map-proper]. Assume the exceptional admissibility of every
morphism below that carries an exceptional inverse image (the
correspondences $c,b$ as total maps, the structure maps of $X,Y,F_c,F_b$,
and $f,g,h,i_c,i_b,d_c,d_b$). Put $q=f\times f$, which is proper by
[lem-trf-fixed-map-proper], so that $bg=qc$ and
$q\Delta_X=\Delta_Yf$. Write $\omega$ for the dualizing complexes and $D$
for the Verdier duals of [def-trf-dualizing-complex], and use the
identifications $Rf_*=Rf_!$, $Rg_*=Rg_!$, $Rq_*=Rq_!$, $Rh_*=Rh_!$ for the
proper maps ([prop-functor-package], clause (3)), the units $\eta$ and
counits $\varepsilon$ of [fix-prop-adjunctions], and the external product
of [def-trf-external-product]. Define:

1. *Kernels.* $P_X=K\boxtimes D_XK$ on $X\times_sX$ and
$P_Y=K'\boxtimes D_YK'$ on $Y\times_sY$.
1. *Trace along $f$.* $\tau_f:Rf_*\omega_X\cong Rf_!Rf^!\omega_Y
\xrightarrow{\varepsilon}\omega_Y$, using
$\omega_X\cong Rf^!\omega_Y$ of [thm-trf-dualizing-complex-composition]
and the counit of $Rf_!\dashv Rf^!$. The same recipe defines
$\tau_h:Rh_*\omega_{F_c}\to\omega_{F_b}$.
1. *Multiplication.* $\mu_f:Rf_*M\otimes Rf_*N\to Rf_*(M\otimes N)$ is the
ordinary adjoint of $f^*(Rf_*M\otimes Rf_*N)=f^*Rf_*M\otimes f^*Rf_*N
\xrightarrow{\varepsilon_f\otimes\varepsilon_f}M\otimes N$.
1. *Dual pushforward.* $\chi_f:Rf_*D_XK\to D_YK'=R\mathcal Hom(K',\omega_Y)$
is the tensor–Hom adjoint of
$$
Rf_*D_XK\otimes Rf_*K\xrightarrow{\ \mu_f\ }Rf_*(D_XK\otimes K)
\xrightarrow{\ Rf_*\mathrm{ev}_K\ }Rf_*\omega_X\xrightarrow{\ \tau_f\ }\omega_Y .
$$
1. *Kernel pushforward.* With the $!$-Künneth isomorphism of
[def-sf-kv-maps] (i) for $f\times f$, put
$$
\Pi_f=\mathrm{Ku}_!(f,f;K,D_XK)^{-1}:K'\boxtimes Rf_*D_XK
\xrightarrow{\ \sim\ }Rq_*P_X,
\qquad
\rho_f=(1\boxtimes\chi_f)\circ\Pi_f^{-1}:Rq_*P_X\longrightarrow P_Y .
$$
1. *Evaluation kernels.* $\delta_K:P_X\to R\Delta_{X*}\omega_X$ is the map
$e_K$ of [lem-trf-trace-map-from-external-duality] (adjoint to evaluation
preceded by the tensor symmetry), and $\delta_{K'}=e_{K'}$ likewise.
1. *Kernel class.* The kernel class of $u$ is the exceptional adjoint
$$
[u]_P:Rc_!A_C\longrightarrow P_X
$$
of $A_C\xrightarrow{\widetilde u}\mathcal H_c(K)\cong Rc^!P_X$, where
$\widetilde u$ is the mate of [def-trf-trace-class-source] and the
isomorphism is the external duality of [thm-trf-verdier-duality]. The
same recipe gives $[v]_P:Rb_!A_D\to P_Y$ for a correspondence $v$ on
$(Y,K')$ supported on $b$.
1. *Support isomorphisms.* $\zeta_c:Ri_{c*}\omega_{F_c}\xrightarrow{\sim}
Rc^!R\Delta_{X*}\omega_X$ is the inverse of the composite
$Rc^!R\Delta_{X*}\omega_X\cong Ri_{c*}Rd_c^!\omega_X\cong Ri_{c*}\omega_{F_c}$
of the right-adjoint form of fixed-square base change
([thm-trf-fixed-point-base-change]) and
[thm-trf-dualizing-complex-composition]; $\zeta_b$ likewise.
1. *Composition and exchange.* $\Xi:Rb_!Rg_*\cong Rq_*Rc_!$ is the
composition law of [thm-sf-comp-composition] for $bg=qc$, and
$$
\mathsf E:Rg_*Rc^!\longrightarrow Rb^!Rq_*
$$
is the exceptional adjoint of
$Rb_!Rg_*Rc^!\xrightarrow{\Xi}Rq_*Rc_!Rc^!\xrightarrow{Rq_*\varepsilon_c}Rq_*$.
We identify $Rq_*R\Delta_{X*}=R\Delta_{Y*}Rf_*$ by $q\Delta_X=\Delta_Yf$.

By construction ([lem-trf-trace-map-from-external-duality]) the trace map
$\mathfrak t_{c,K}$ is $R\Gamma(C,-)$ of
$\zeta_c^{-1}\circ Rc^!\delta_K\circ(\mathcal H_c(K)\cong Rc^!P_X)$.
