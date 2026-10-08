+++
id = "def-pur-tate-datum"
kind = "definition"
title = "Strict Weil data and the Tate datum"
order = 2236
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-scheme-geometric-frobenius", "def-pur-smooth-pullback-exchange", "def-sbc-smooth-morphisms", "def-weil-algebraically-closed-coefficients", "def-weil-frobenius-coefficient-twists", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
geometric-Frobenius datum,
and a coefficient ring $\Lambda\in\{A_{E,n},\mathcal O_E,E,\Qlb\}$. A
*strict geometric-Weil datum* on $K\in D^b_{ctf}(Y,\Lambda)$ is a
specified isomorphism in the ordinary triangulated category

$$
\varphi_K:Lg_{Y,\gamma}^*K\xrightarrow{\ \sim\ }K;
$$

for $\Lambda=\mathcal O_E$ such a datum is a normalized system of
finite-stage data compatible with the reductions, for $\Lambda=E$ an
object obtained from an $\mathcal O_E$-datum by inverting $\varpi$,
and for
$\Lambda=\Qlb$ a datum over some finite $E/\Ql$,
modulo further finite coefficient extension (as in
[def-weil-weil-sheaf-complex], with the
rationalized common-stage
conventions). In every case the forgetful object lies in
$D^b_{ctf}(Y,\Lambda)$ and $\varphi_K$ denotes the resulting typed
isomorphism; its scheme-Frobenius form is

$$
u_K=\varphi_K\circ\kappa_{Y,K}:L\Phi_Y^*K\longrightarrow K.
$$

The Tate line carries its canonical
datum, the twist normalization of
[def-weil-frobenius-coefficient-twists],

$$
\tau_1:Lg_{Y,\gamma}^*\Lambda_Y(1)\xrightarrow{\ \sim\ }\Lambda_Y(1),
\quad
\tau_r:Lg_{Y,\gamma}^*\Lambda_Y(r)\xrightarrow{\ \sim\ }\Lambda_Y(r),
$$

on which geometric Frobenius acts by $q^{-1}$ on $\Lambda(1)$ and by
$q^{-r}$ on $\Lambda(r)$. The induced datum on the source of smooth
purity is

$$
\begin{aligned}
\varphi^{\mathrm{pur}}_{f,K}:
Lg_{X,\gamma}^*\bigl(Lf^*K(d)[2d]\bigr)
&\xrightarrow{\ \sim\ }
Lf^*Lg_{Y,\gamma}^*K\otimes^L_{\Lambda_X}
Lg_{X,\gamma}^*\Lambda_X(d)[2d]\\
&\xrightarrow{\ Lf^*\varphi_K\otimes\tau_d\ }
Lf^*K(d)[2d],
\end{aligned}
$$

and the datum on the exceptional inverse image is

$$
\begin{aligned}
\varphi^!_{f,K}:Lg_{X,\gamma}^*Rf^!K
&\xrightarrow{\ \operatorname{Ex}^{!,\mathrm{sm}}_{f,g_{Y,\gamma},K}\ }
Rf^!Lg_{Y,\gamma}^*K
\xrightarrow{\ Rf^!(\varphi_K)\ }Rf^!K,
\end{aligned}
$$

using the smooth pullback exchange of [def-pur-smooth-pullback-exchange]
for the first Cartesian square of [def-pur-scheme-geometric-frobenius].
