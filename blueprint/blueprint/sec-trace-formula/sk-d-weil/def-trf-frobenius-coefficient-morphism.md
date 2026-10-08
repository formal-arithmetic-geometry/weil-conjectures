+++
id = "def-trf-frobenius-coefficient-morphism"
kind = "definition"
title = "Frobenius coefficient morphisms"
order = 2296
uses = ["def-trf-coefficient-conventions", "def-trf-global-operator", "def-trf-graph-correspondence", "def-trf-iterated-weil-map", "def-trf-scheme-frobenius", "def-trf-strict-weil-complex", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum and the coefficient conventions of
[def-trf-coefficient-conventions], let $X_0$ be a separated
finite-type $k_0$-scheme, put $X=X_0\times_{k_0}k$, and let $\Phi$ be
the $q$-power scheme Frobenius of [def-trf-scheme-frobenius], with
iterates $\Phi^m$. Let $K\in D^b_{ctf}(X,A)$.

1. A *Frobenius coefficient morphism* on $K$ is an arbitrary morphism
$$
\psi:L\Phi^*K\longrightarrow K
$$
in the derived category of $X$; no invertibility is required.
1. Its *iterates* $\psi_m:L\Phi^{m*}K\to K$, $m\geq1$, are defined
recursively by $\psi_1=\psi$ and
$$
\psi_m:\;L\Phi^{m*}K\xrightarrow{\ \sim\ }
L\Phi^*L\Phi^{(m-1)*}K
\xrightarrow{\ L\Phi^*\psi_{m-1}\ }L\Phi^*K
\xrightarrow{\ \psi\ }K,
$$
where the first arrow is the composition isomorphism of derived
pullback for $\Phi^m=\Phi^{m-1}\circ\Phi$; thus $\psi_m$ is the
composite of the pulled-back copies $L\Phi^{i*}\psi$,
$0\leq i\leq m-1$, exactly as for the iterated Weil isomorphism of
[def-trf-iterated-weil-map].
1. Its *graph map* in degree $m$ is the graph correspondence of
[def-trf-graph-correspondence] attached to $(h,v)=(\Phi^m,\psi_m)$:
$$
c_m=(c_1,c_2)=(\operatorname{id}_X,\Phi^m),\qquad u=\psi_m:
Lc_2^*K=L\Phi^{m*}K\longrightarrow K=Rc_1^!K .
$$
1. Its *global operator* in degree $m$ is
$$
F_{c,m}(\psi)=T_{c_m}(\psi_m):R\Gamma_c(X,K)\longrightarrow R\Gamma_c(X,K),
$$
the global operator of [def-trf-global-operator] of the graph map. It
is defined because the ordinary leg $c_2=\Phi^m$ is finite
([def-trf-scheme-frobenius]), hence proper
([def-weil-scheme-morphism-properties]), and the exceptional leg
$c_1=\operatorname{id}_X$ is admissible with $Rc_1^!=\operatorname{id}$.

*Example.* For a strict Weil complex $(K,\varphi)$ of
[def-trf-strict-weil-complex], the scheme-Frobenius map
$u_1=\varphi\circ\kappa_K:L\Phi^*K\xrightarrow{\sim}K$ of
[def-trf-iterated-weil-map] is an (invertible) Frobenius coefficient
morphism; the notion above drops the invertibility, and the iterates,
graph map and global operator are given by the same composites.
