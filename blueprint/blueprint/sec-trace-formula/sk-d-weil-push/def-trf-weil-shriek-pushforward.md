+++
id = "def-trf-weil-shriek-pushforward"
kind = "definition"
title = "Weil $!$-pushforward along a separated morphism"
order = 2364
uses = ["d-relative-frob", "def-exchange-projection", "def-trf-frobenius-coefficient-morphism", "def-trf-iterated-weil-map", "def-trf-scheme-frobenius", "def-trf-strict-weil-complex", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-scheme-morphism-properties", "fix-lem-exchanges", "i-relative-frob", "i-topology", "prop-functor-package", "prop-trf-scheme-galois-comparison"]
+++
Fix the global finite-field datum and the coefficient ring
$A=A_{E,n}$. Let $f_0:X_0\to Y_0$ be a separated morphism of
separated finite-type $k_0$-schemes, with geometric base change
$f:X\to Y$, and write $\Phi_X,\Phi_Y$ for the $q$-power scheme
Frobenii of [def-trf-scheme-frobenius]. For $m\geq1$ use the
relative Frobenius factorization of [d-relative-frob]:

$$
X'_m=Y\times_{\Phi_Y^m,Y,f}X,\qquad
p_m:X'_m\to X,\quad f'_m:X'_m\to Y,\qquad
r_m=(f,\Phi_X^m):X\to X'_m,
$$

so that $p_mr_m=\Phi_X^m$ and $f'_mr_m=f$; this uses
$f\Phi_X^m=\Phi_Y^mf$, which holds because $\Phi^m$ is the base
change of the $q^m$-power Frobenius of $k_0$-schemes, which commutes
with every $k_0$-morphism.

1. For $K\in D^b_{ctf}(X,A)$ the *Frobenius comparison*
$\theta_{f,m}=\theta_{f,m,K}$ is the composite
$$
L\Phi_Y^{m*}Rf_!K
\xrightarrow[\sim]{\operatorname{Ex}_!}Rf'_{m!}Lp_m^*K
\xrightarrow{Rf'_{m!}(\eta_{r_m})}
Rf'_{m!}Rr_{m*}Lr_m^*Lp_m^*K
\xrightarrow{\ \sim\ }Rf_!L\Phi_X^{m*}K .
$$
The first arrow is the compact-support exchange of
[def-exchange-projection] for the Cartesian square defining $X'_m$,
an isomorphism by arbitrary base change ([prop-functor-package],
clause (4)). The second arrow is $Rf'_{m!}$ applied to the unit of
$Lr_m^*\dashv Rr_{m*}$ of [def-weil-derived-direct-image]. The last
arrow is $Rr_{m*}\simeq Rr_{m!}$ for the finite, hence proper, map
$r_m$, the composition law
$Rf'_{m!}Rr_{m!}\simeq R(f'_mr_m)_!=Rf_!$ ([prop-functor-package],
clause (3)), and $Lr_m^*Lp_m^*\simeq L(p_mr_m)^*=L\Phi_X^{m*}$
([def-weil-derived-pullback-tensor-hom]).
The middle unit is invertible: $r_m$ is a finite universal
homeomorphism by [i-relative-frob], so $Lr_m^*$ is an equivalence
on $D^b_{ctf}$ with invertible unit by [i-topology], applied to
$Lp_m^*K\in D^b_{ctf}(X'_m,A)$. Hence $\theta_{f,m}$ is an
isomorphism, natural in $K$ because each of its three arrows is
([fix-lem-exchanges], clause (1)).
1. For a Frobenius coefficient morphism $u:L\Phi_X^*K\to K$ of
[def-trf-frobenius-coefficient-morphism] (no invertibility
assumed), the *Weil $!$-pushforward* of $(K,u)$ along $f$ is the
pair $(Rf_!K,\psi)$ with
$$
\psi=Rf_!u\circ\theta_{f,1}:\;
L\Phi_Y^*Rf_!K\xrightarrow{\ \theta_{f,1}\ }Rf_!L\Phi_X^*K
\xrightarrow{\ Rf_!u\ }Rf_!K .
$$
It lies in $D^b_{ctf}(Y,A)$ by [prop-functor-package], and $\psi$
is a Frobenius coefficient morphism on $Rf_!K$.
1. In particular, for a strict Weil complex $(K,\varphi)$ of
[def-trf-strict-weil-complex], take $u=u_1=\varphi\circ\kappa_K$,
its scheme-Frobenius map of [def-trf-iterated-weil-map], with
$\kappa$ of [prop-trf-scheme-galois-comparison]. Then $\psi$ is a
composite of two isomorphisms, so $(Rf_!K,\psi)$ is a pushforward
with invertible scheme-Frobenius structure.
