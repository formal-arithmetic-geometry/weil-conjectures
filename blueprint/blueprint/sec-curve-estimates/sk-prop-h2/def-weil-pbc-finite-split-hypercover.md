+++
id = "def-weil-pbc-finite-split-hypercover"
kind = "definition"
title = "Finite split etale hypercovers"
order = 946
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions"]
+++
Let $X$ be quasi-compact and quasi-separated
[def-weil-pbc-scheme-conventions]. An augmented simplicial $X$-scheme
consists of schemes $U_n$, face maps $d_i:U_n\to U_{n-1}$, degeneracy maps
$s_i:U_n\to U_{n+1}$, and $U_0\to X$, satisfying the simplicial identities.
Its *matching scheme* $M_n(U)$ is the finite limit specifying all compatible
proper faces of an $n$-simplex; $M_0(U)=X$ and $M_1(U)=U_0\times_XU_0$. It is
a *split etale hypercover* if every $U_n\to M_n(U)$ is an etale covering
[def-weil-pbc-etale-site] and there are specified nondegenerate summands
$N_m$ with

$$
 U_n=\coprod_{[n]\twoheadrightarrow[m]}N_m.
$$

Here $[n]=\{0,\ldots,n\}$, and the index runs over order-preserving
surjections. We call it *finite in each degree* if every $N_m$ is a finite
disjoint union of quasi-compact quasi-separated etale $X$-schemes of finite
presentation. A *truncation through degree $r$* retains all these data for
$n\leq r$. A refinement is a morphism of augmented simplicial schemes over
$X$; two refinements are identified when they are simplicially homotopic. For
an abelian sheaf $F$, set

$$
 C^n(U,F)=F(U_n),\qquad
 \delta=\sum_{i=0}^{n+1}(-1)^i d_i^*:C^n(U,F)\longrightarrow C^{n+1}(U,F).
$$

In particular, computing $H^q(C^\bullet(U,F))$ requires degrees through
$q+1$, even though a cocycle itself has degree $q$.
