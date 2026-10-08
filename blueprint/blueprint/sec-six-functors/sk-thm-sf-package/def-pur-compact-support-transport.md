+++
id = "def-pur-compact-support-transport"
kind = "definition"
title = "Compact-support transport of a Weil datum"
order = 2237
uses = ["def-coefficient-twists-detailed", "def-exchange-projection", "def-pur-conventions", "def-pur-scheme-geometric-frobenius", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
geometric-Frobenius datum,
and let $M\in D^b_{ctf}(X,\Lambda)$ carry a strict Weil datum
$\varphi_M:Lg_{X,\gamma}^*M\cong M$. The compact-support transport of the
datum is

$$
\varphi_{f_!M}:Lg_{Y,\gamma}^*Rf_!M
\xrightarrow{\ \operatorname{Ex}_!\ }
Rf_!Lg_{X,\gamma}^*M
\xrightarrow{\ Rf_!(\varphi_M)\ }Rf_!M,
$$

the first arrow being the compact-support base change of
[def-exchange-projection] for the first Cartesian square of
[def-pur-scheme-geometric-frobenius]. Its scheme-Frobenius form is

$$
u_N=\varphi_N\circ\kappa_{T,N}:L\Phi_T^*N\longrightarrow N
$$

for every object $N$ on $T=X$ or $Y$ carrying a datum, as in
[def-pur-scheme-geometric-frobenius].
