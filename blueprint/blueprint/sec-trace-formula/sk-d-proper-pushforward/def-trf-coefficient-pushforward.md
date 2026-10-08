+++
id = "def-trf-coefficient-pushforward"
kind = "definition"
title = "Coefficient pushforward of a correspondence"
order = 2326
uses = ["def-exchange-projection", "def-trf-admissibility", "def-trf-correspondence", "def-trf-fixed-scheme", "fix-lem-exchanges", "fix-prop-adjunctions", "prop-functor-package", "thm-sf-comp-composition", "thm-sf-dual-base-change"]
+++
Fix the global finite-field datum and the coefficient conventions,
$A=A_{E,n}$, $s=\Spec k$; all functors are derived, and we write
$c_2^*$, $c_1^!$ for $Lc_2^*$, $Rc_1^!$. Let
$c=(c_1,c_2):C\to X\times_sX$ be an admissible cohomological
correspondence of [def-trf-correspondence], let $K\in D^b_{ctf}(X,A)$
and let $u:c_2^*K\to c_1^!K$ be a correspondence. Let
$b=(b_1,b_2):D\to Y\times_sY$ be a second admissible correspondence. A
*proper pushforward diagram* $(f,g):(C,c)\to(D,b)$ consists of proper
morphisms

$$
f:X\longrightarrow Y,\qquad g:C\longrightarrow D,
\qquad b_ig=fc_i\quad(i=1,2).
$$

No Cartesian condition is imposed on either leg square
$(c_i,g,b_i,f)$, and $X,Y,C,D$ need not be proper over $s$. Put
$K'=Rf_*K$. Write $\eta_g:\operatorname{id}\to Rg_*g^*$ and
$\varepsilon_f:f^*Rf_*\to\operatorname{id}$ for the unit and counit of
the ordinary adjunctions, and $\varepsilon_{c_1}:Rc_{1!}c_1^!\to\operatorname{id}$
for the counit of $Rc_{1!}\dashv c_1^!$, all as in [fix-prop-adjunctions].

1. *The ordinary half.* Let
$$
\begin{aligned}
\gamma:b_2^*K'
&\xrightarrow{\ \eta_g\ }Rg_*g^*b_2^*Rf_*K
= Rg_*c_2^*f^*Rf_*K\\
&\xrightarrow{\ Rg_*c_2^*\varepsilon_f\ }Rg_*c_2^*K,
\end{aligned}
$$
the equality being the pullback composition $g^*b_2^*=(b_2g)^*=(fc_2)^*=c_2^*f^*$.
1. *The exceptional half.* Since $f$ and $g$ are proper,
$Rf_*=Rf_!$ and $Rg_*=Rg_!$ ([prop-functor-package], clause (3)), and the
composition law of [thm-sf-comp-composition] applied to $b_1g=fc_1$ gives
$\Xi_1:Rb_{1!}Rg_*\cong R(b_1g)_!=R(fc_1)_!\cong Rf_!Rc_{1!}$. Let
$$
\delta:Rg_*c_1^!K\longrightarrow b_1^!K'
$$
be the exceptional adjoint (for $Rb_{1!}\dashv b_1^!$) of
$$
Rb_{1!}Rg_*c_1^!K\xrightarrow{\ \Xi_1\ }Rf_!Rc_{1!}c_1^!K
\xrightarrow{\ Rf_!\varepsilon_{c_1}\ }Rf_!K=K'.
$$
1. The *coefficient pushforward* of $u$ is
$$
[f,g]_!u:=\delta\circ Rg_*u\circ\gamma:\
b_2^*K'\longrightarrow b_1^!K',
$$
a correspondence on $(Y,K')$ supported on $b$ (Varshavsky, loc. cit.,
1.2.4).
1. *The induced map of fixed schemes.* Let $F_c=\operatorname{Fix}(c)$
and $F_b=\operatorname{Fix}(b)$ be the fixed schemes of
[def-trf-fixed-scheme], with projections $i_c:F_c\to C$, $d_c:F_c\to X$
and $i_b:F_b\to D$, $d_b:F_b\to Y$. Since
$b\,g\,i_c=(f\times f)\,c\,i_c=(f\times f)\Delta_Xd_c=\Delta_Y\,f\,d_c$,
the universal property of $F_b=D\times_{Y\times_sY,\Delta_Y}Y$ gives a
unique morphism
$$
h:F_c\longrightarrow F_b,\qquad i_bh=g\,i_c,\qquad d_bh=f\,d_c .
$$
Its properness, and hence the Borel–Moore pushforward of the trace
class along $h$, are established in the next lemma of this block.

*The Cartesian case.* Neither construction uses a Cartesian
square, but they reduce to the familiar maps when the squares are
Cartesian. The recipe for $\gamma$ is the recipe of the exchange
$\operatorname{Ex}_*$ of [def-exchange-projection] (the adjoint of the
counit composed with the identification of pullbacks); so if
$(c_2,g,b_2,f)$ is Cartesian, $\gamma=\operatorname{Ex}_*$ is the proper
base-change isomorphism $b_2^*Rf_*\cong Rg_*c_2^*$ of
[prop-functor-package], clause (4). The map $\delta$ is the exchange map
of [def-trf-admissibility] formed from the composition law and the
exceptional counits; if $(c_1,g,b_1,f)$ is Cartesian, it is inverse to the
dual base-change isomorphism $b_1^!Rf_*\cong Rg_*c_1^!$ of
[thm-sf-dual-base-change] (applied with $b_1$ as the exceptional map and
$f$ as the proper map). Indeed, the latter is the mate of
$\operatorname{Ex}_!$, and $\operatorname{Ex}_!$ is compatible with the
composition law ([fix-lem-exchanges], item 4) and with the adjunctions
([fix-prop-adjunctions], item 4), so the two mates are mutually inverse.
