+++
id = "sk-d-proper-pushforward"
kind = "section"
title = "Proper pushforward of a correspondence and its trace"
order = 2325
uses = ["sk-d-corr", "sk-d-integral", "sk-d-six", "sk-d-trace-class"]
lean = ["AlgebraicGeometry.ProEtale.ProperPushforwardDiagram"]
+++
*Definition (sketch).*

Let $(C,c,u)$ be an endocorrespondence on $(X,K)$ and
let $b=(b_1,b_2):D\to Y\times Y$. A proper pushforward diagram consists
of proper $f:X\to Y$, $g:C\to D$ with $b_i g=fc_i$ for $i=1,2$.
Put $K'=Rf_*K$. Using the adjunctions and composition maps, set

$$
\begin{aligned}
\gamma:b_2^*K'&\xrightarrow{\eta_g^*}Rg_*g^*b_2^*Rf_*K
\simeq Rg_*c_2^*f^*Rf_*K\\
&\xrightarrow{Rg_*c_2^*\varepsilon_f^*}Rg_*c_2^*K.
\end{aligned}
$$

Let $\delta:Rg_*c_1^!K\to b_1^!K'$ be the exceptional adjoint of

$$
Rb_{1!}Rg_*c_1^!K\simeq Rf_!Rc_{1!}c_1^!K
\xrightarrow{Rf_!\varepsilon_{c_1}^!}Rf_!K\simeq K',
$$

where properness identifies $Rg_*=Rg_!$ and $Rf_*=Rf_!$. Define

$$
[f,g]_!u:=\delta\circ Rg_*u\circ\gamma:
b_2^*K'\longrightarrow b_1^!K'.
$$

The relations induce $h:\Fix(c)\to\Fix(b)$. For proper $h$, the
proper pushforward of the trace class is
$h_*\Tr_c(u):A_{\Fix(b)}\to\omega_{\Fix(b)}$, using the
Borel–Moore pushforward.
No Cartesian condition on either leg square enters these constructions.

Uses: [sk-d-corr], [sk-d-integral], [sk-d-six], [sk-d-trace-class]
