+++
id = "lem-pc-projective-space-canonical"
kind = "lemma"
title = "The canonical sheaf of projective space"
order = 620
uses = ["def-pc-proj", "def-pc-projective-space-twist", "def-sc-invertible-module", "lem-pc-projective-space-twist-cohomology"]
+++
Let $A$ be a commutative ring, $n\ge1$, and $P=\mathbf P^n_A$ with
standard opens $U_i=D_+(x_i)=\operatorname{Spec}R_i$, where
$R_i=A[x_k/x_i:k\ne i]$ is a polynomial ring in $n$ variables
([def-pc-proj]). Let $\Omega^1_{P/A}$ be the sheaf of relative
differentials: the $\mathcal O_P$-module whose restriction to $U_i$ is
associated with the module $\Omega^1_{R_i/A}$ of Kähler differentials,
glued along the canonical isomorphisms
$\Omega^1_{R_i/A}\otimes_{R_i}R_{ij}\cong\Omega^1_{R_{ij}/A}\cong
\Omega^1_{R_j/A}\otimes_{R_j}R_{ij}$, where
$R_{ij}=\Gamma(U_i\cap U_j,\mathcal O_P)$ is a localization of both
$R_i$ and $R_j$. Put
$\omega_P:=\Lambda^n\Omega^1_{P/A}$ and, on $U_i$,

$$
\eta_i:=(-1)^i\bigwedge_{k\ne i}d(x_k/x_i)
$$

(wedge over $k\in\{0,\ldots,n\}\smallsetminus\{i\}$ in increasing
order). Then $\Omega^1_{P/A}$ is locally free of rank $n$, $\omega_P$ is
an invertible module ([def-sc-invertible-module]) with basis $\eta_i$
on $U_i$, and there is an isomorphism

$$
\omega_P\;\xrightarrow{\ \sim\ }\;\mathcal O_P(-n-1)
$$

onto the twist of [def-pc-projective-space-twist], sending $\eta_i$ to
$e_i^{(-n-1)}$ on each $U_i$. In particular
$H^n(P,\omega_P)\cong A$
([lem-pc-projective-space-twist-cohomology] (ii)). For $n=1$ and
$A=k$, with $t=x_1/x_0$ and $s=x_0/x_1$, this is
$\omega_{\mathbf P^1}\cong\mathcal O(-2)$ with $\eta_0=dt$,
$\eta_1=-ds$ and $dt=-t^2ds$.

## Proof

Kähler differentials commute with localization, which gives the
canonical isomorphisms used for the gluing; they are compatible on
triple intersections because all of them are the canonical
identifications with the differentials of the common localization
$\Gamma(U_i\cap U_j\cap U_l,\mathcal O_P)$. For the polynomial ring
$R_i$, $\Omega^1_{R_i/A}$ is free with basis $d(x_k/x_i)$, $k\ne i$, so
$\Omega^1_{P/A}$ is locally free of rank $n$, and
$\Lambda^n\Omega^1_{R_i/A}$ is free of rank one with basis $\eta_i$.

Fix $i\ne j$ and write $t_k=x_k/x_j$ ($k\ne j$) for the coordinates of
$U_j$; on $U_i\cap U_j$ the element $t_i$ is a unit, and
$x_j/x_i=t_i^{-1}$, $x_k/x_i=t_k/t_i$ for $k\notin\{i,j\}$. Hence

$$
d(x_j/x_i)=-t_i^{-2}\,dt_i,\qquad
d(x_k/x_i)=t_i^{-1}dt_k-t_kt_i^{-2}\,dt_i\quad(k\notin\{i,j\}).
$$

In the wedge $\bigwedge_{k\ne i}d(x_k/x_i)$ the factor in position $j$
is a multiple of $dt_i$, so the $dt_i$-terms of the other factors
contribute zero ($dt_i\wedge dt_i=0$). The wedge equals
$-t_i^{-2}\cdot t_i^{-(n-1)}$ times the wedge of the $dt_k$, $k\ne j$,
taken in the order of the indices $\{0,\ldots,n\}\smallsetminus\{i\}$
with $dt_i$ in the slot of $j$. Moving $dt_i$ to its increasing
position passes the $|i-j|-1$ factors $dt_k$ with $k$ strictly between
$i$ and $j$, so

$$
\bigwedge_{k\ne i}d(x_k/x_i)=(-1)^{|i-j|}\,t_i^{-(n+1)}
\bigwedge_{k\ne j}dt_k,
\qquad\text{i.e.}\qquad
\eta_i=(-1)^i(-1)^{i+j}(x_i/x_j)^{-(n+1)}(-1)^j\eta_j
=(x_i/x_j)^{-(n+1)}\eta_j .
$$

This is exactly the transition rule
$e_i^{(-n-1)}=(x_i/x_j)^{-n-1}e_j^{(-n-1)}$ of
[def-pc-projective-space-twist]. Hence the isomorphisms
$\omega_P|_{U_i}\to\mathcal O_P(-n-1)|_{U_i}$, $\eta_i\mapsto
e_i^{(-n-1)}$, agree on the overlaps, and they glue to an isomorphism
of $\mathcal O_P$-modules (the sheaf axiom on the cover by the $U_i$;
the glued map is an isomorphism because it is one locally). The
statement on $H^n$ follows from the rank-one basis of
$H^n(P,\mathcal O_P(-n-1))$. For $n=1$: $\eta_0=d(x_1/x_0)=dt$,
$\eta_1=-d(x_0/x_1)=-ds$, and the rule reads
$dt=(x_0/x_1)^{-2}(-ds)=-t^2ds$, in accordance with $s=t^{-1}$.
