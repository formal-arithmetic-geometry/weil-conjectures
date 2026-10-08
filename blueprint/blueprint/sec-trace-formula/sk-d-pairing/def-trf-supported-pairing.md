+++
id = "def-trf-supported-pairing"
kind = "definition"
title = "The supported pairing recipe"
order = 2311
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-correspondence-between-pairs", "def-trf-dualizing-complex", "def-trf-fixed-scheme", "def-trf-integration", "def-trf-local-term", "def-trf-supported-class", "def-weil-derived-pullback-tensor-hom", "lem-trf-correspondence-class", "prop-functor-package", "prop-trf-exceptional-kunneth", "thm-trf-dualizing-complex-composition", "thm-trf-kunneth-verdier"]
+++
Fix the coefficient conventions of
[def-trf-coefficient-conventions], $A=A_{E,n}$, $s=\Spec k$. Let
$X,Y$ be separated finite-type $k$-schemes whose structure morphisms
$a_X,a_Y$ are exceptionally admissible
([def-trf-admissibility]), with the dualizing data
$\omega_X,\omega_Y$, $D_X,D_Y$ and evaluations of
[def-trf-dualizing-complex], and let
$K\in D^b_{ctf}(X,A)$, $L\in D^b_{ctf}(Y,A)$. Put

$$
Z:=Y\times_sX,\qquad p_1:Z\to Y,\quad p_2:Z\to X,
$$

and let $\tau:X\times_sY\xrightarrow{\sim}Y\times_sX$ exchange the
factors. External products are
$M\boxtimes_A^{\mathrm L}N:=Lp_1^*M\otimes_A^{\mathrm L}Lp_2^*N$
([def-weil-derived-pullback-tensor-hom]).

*Opposite pairs.* Let $(C,c,u)$ be a correspondence from $(X,K)$ to
$(Y,L)$ and $(D,d,v)$ an opposite correspondence, in the sense of
[def-trf-correspondence-between-pairs] (which generalizes
[def-trf-correspondence], the case $(Y,L)=(X,K)$); such a pair is an
*opposite pair*. With $\bar d=\tau d:D\to Z$ and
$E=E(C,D)=C\times_{c,Z,\bar d}D$ as there, write $e_C:E\to C$,
$e_D:E\to D$ for the projections and
$e:=c\,e_C=\bar d\,e_D:E\to Z$ (all maps separated of finite type, and
exceptionally admissible where an exceptional functor is applied; in
particular $c$, $\bar d$, $e$ and $p_1$ are exceptionally admissible).

*Step 1: the supported classes.* Let
$[u]\in H^0_C\bigl(Z,\RHom_A(Lp_2^*K,Rp_1^!L)\bigr)$ be the class of
$u$ given by [lem-trf-correspondence-class], a class supported on $c$
in the sense of [def-trf-supported-class].
The Künneth–Verdier
isomorphism of [thm-trf-kunneth-verdier] for the product $Y\times_sX$,
with $M=L$ and $N=K$,
$\kappa_{L,K}:L\boxtimes_A^{\mathrm L}D_XK\xrightarrow{\sim}
\RHom_A(Lp_2^*K,Rp_1^!L)$, gives the class supported on $c$

$$
\widetilde u:=\kappa_{L,K}^{-1}\circ[u]:
Rc_!A_C\longrightarrow P:=L\boxtimes_A^{\mathrm L}D_XK .
$$

The same construction applied to $(D,d,v)$ on $X\times_sY$ gives
$\kappa_{K,L}^{-1}\circ[v]:Rd_!A_D\to K\boxtimes_A^{\mathrm L}D_YL$;
applying the isomorphism $R\tau_!=R\tau_*$ (with
$R\tau_!Rd_!\simeq R\bar d_!$ by [prop-functor-package], item (3))
and the symmetry of $\otimes_A^{\mathrm L}$, which identifies
$R\tau_*(K\boxtimes_A^{\mathrm L}D_YL)$ with
$D_YL\boxtimes_A^{\mathrm L}K$ on $Z$, gives

$$
\widetilde v:R\bar d_!A_D\longrightarrow Q:=D_YL\boxtimes_A^{\mathrm L}K .
$$

*Step 2: the support of the product.* The projection formula
([prop-functor-package], item (5)), the base change
$Lc^*R\bar d_!\simeq Re_{C!}Le_D^*$ in the Cartesian square defining
$E$ ([prop-functor-package], item (4)), and the composition
$Rc_!Re_{C!}\simeq Re_!$ ([prop-functor-package], item (3)) give the
canonical isomorphism

$$
\mu:Re_!A_E\simeq Rc_!Re_{C!}Le_D^*A_D
\simeq Rc_!\bigl(Lc^*R\bar d_!A_D\bigr)
\simeq Rc_!A_C\otimes_A^{\mathrm L}R\bar d_!A_D .
$$

*Step 3: the pairing.* Using the symmetry of
$\otimes_A^{\mathrm L}$ and the monoidality of $Lp_i^*$,
$P\otimes_A^{\mathrm L}Q\simeq
Lp_1^*(D_YL\otimes_A^{\mathrm L}L)\otimes_A^{\mathrm L}
Lp_2^*(D_XK\otimes_A^{\mathrm L}K)$; the two Verdier evaluations
$\operatorname{ev}_L$, $\operatorname{ev}_K$ of
[def-trf-dualizing-complex] map this to
$\omega_Y\boxtimes_A^{\mathrm L}\omega_X$, and the exceptional
Künneth isomorphism $\alpha$ of [prop-trf-exceptional-kunneth] for
$f_1=a_Y$, $f_2=a_X$, $L_1=L_2=A_s$ (note $a_Y\times a_X=a_Z$ and
$A_s\boxtimes_A^{\mathrm L}A_s=A_s$ on $s\times_ss=s$) is the product
comparison $\omega_Y\boxtimes_A^{\mathrm L}\omega_X\simeq\omega_Z$.
Composing,

$$
\sigma_{u,v}:
Re_!A_E\xrightarrow{\ \mu\ }
Rc_!A_C\otimes_A^{\mathrm L}R\bar d_!A_D
\xrightarrow{\widetilde u\otimes\widetilde v}
P\otimes_A^{\mathrm L}Q
\xrightarrow{\operatorname{ev}_L\boxtimes\operatorname{ev}_K}
\omega_Y\boxtimes_A^{\mathrm L}\omega_X
\xrightarrow{\ \alpha\ }\omega_Z .
$$

The *Borel–Moore section* (of [def-trf-integration])

$$
\langle u,v\rangle_{\mathrm{LV}}:A_E\longrightarrow\omega_E
$$

is the exceptional adjoint of $\sigma_{u,v}$: its image under
$\Hom_Z(Re_!A_E,\omega_Z)\cong\Hom_E(A_E,Re^!\omega_Z)$, followed by
the identification $Re^!\omega_Z\simeq\omega_E$ of
[thm-trf-dualizing-complex-composition].

*The diagonal case.* For $(Y,L)=(X,K)$ take the opposite
correspondence $D=X$, $d=\Delta_X$, $v=1_K$ (both legs are
$\operatorname{id}_X$); then $\bar d=\Delta_X$ and
$E=C\times_{X\times_sX,c,\Delta_X}X=\Fix(c)$ is the fixed scheme of
[def-trf-fixed-scheme]. Abbreviate
$\LT_B(u,v)=\LT_B(\langle u,v\rangle_{\mathrm{LV}})$, the local term of
[def-trf-local-term] (for $B$ a proper open-and-closed component). That
$\langle u,1_K\rangle_{\mathrm{LV}}$ is the trace class of
[def-trf-trace-class] is [lem-trf-trace-class-diagonal-pairing].
