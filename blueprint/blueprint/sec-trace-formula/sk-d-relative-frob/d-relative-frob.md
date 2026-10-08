+++
id = "d-relative-frob"
kind = "definition"
title = "The relative Frobenius factorization"
order = 2360
uses = ["def-trf-coefficient-conventions", "def-trf-scheme-frobenius"]
+++
Fix the global finite-field datum $p,a,q,k_0,k$ and the coefficient
conventions of [def-trf-coefficient-conventions]. Let
$f_0:X_0\to Y_0$ be a morphism of separated finite-type
$k_0$-schemes, write $f:X\to Y$ for its base change to $k$, and let
$\Phi_X,\Phi_Y$ be the $q$-power scheme Frobenii of
[def-trf-scheme-frobenius]. For $m\geq1$ put

$$
X'_m=Y\times_{\Phi_Y^m,Y,f}X,
\quad p_m:X'_m\to X,\quad f'_m:X'_m\to Y,
\quad r_m=(f,\Phi_X^m):X\to X'_m,
$$

where $f'_m$ and $p_m$ are the first and second projections, so
that $\Phi_Y^mf'_m=fp_m$. The map $r_m$ is defined because
$\Phi_Y^mf=f\Phi_X^m$: with $Q=q^m$, the maps $\Phi^m$ are the base
changes $\Phi_0^m\times\operatorname{id}_k$ of the absolute
$Q$-power Frobenii of the $k_0$-schemes $X_0$, $Y_0$ (their affine
incarnation is $a\mapsto a^Q$), and absolute Frobenius commutes with
every morphism of $\mathbf F_p$-schemes. By construction

$$
p_mr_m=\Phi_X^m,\qquad f'_mr_m=f .
$$

*The relative Frobenius.* Write $F_{X_0},F_{Y_0}$ for the absolute
$Q$-power Frobenii of $X_0,Y_0$ and put
$X_0^{(Q)}=Y_0\times_{F_{Y_0},Y_0,f_0}X_0$. The *relative
$Q$-power Frobenius* of $X_0$ over $Y_0$ is
$F_{X_0/Y_0}=(f_0,F_{X_0}):X_0\to X_0^{(Q)}$. Since fibre products
commute with the base change $k_0\to k$ and
$\Phi=\Phi_0\times\operatorname{id}_k$,

$$
X'_m=X_0^{(Q)}\times_{k_0}k,\qquad
r_m=F_{X_0/Y_0}\times_{k_0}\operatorname{id}_k .
$$

Affine-locally, for $\operatorname{Spec}R\subseteq Y_0$ and
$\operatorname{Spec}S\subseteq f_0^{-1}(\operatorname{Spec}R)$, the
scheme $X_0^{(Q)}$ is $\operatorname{Spec}(R\otimes_{F,R}S)$, the
tensor product along $F:R\to R$, $r\mapsto r^Q$, on the left factor,
and $F_{X_0/Y_0}$ is given by

$$
R\otimes_{F,R}S\longrightarrow S,\qquad r'\otimes s\longmapsto
f_0^\#(r')\,s^Q ,
$$

which is well defined because $r'r^Q\otimes s$ and $r'\otimes f_0^\#(r)s$
have the same image $f_0^\#(r')f_0^\#(r)^Qs^Q$.
