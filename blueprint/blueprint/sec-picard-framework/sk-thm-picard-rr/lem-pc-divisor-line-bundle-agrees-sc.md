+++
id = "lem-pc-divisor-line-bundle-agrees-sc"
kind = "lemma"
title = "$\\mathcal{O}_X(D)$ agrees with the divisor module of file 06"
order = 722
uses = ["def-pc-divisor-line-bundle", "def-sc-divisor", "def-sc-effective-cartier-divisor", "lem-sc-point-cartier", "lem-sc-regular-dim1-dvr", "lem-sc-smooth-regular"]
+++
Let $k$ be a field, $C$ a smooth connected curve over $k$
and $D=\sum_{i=1}^m n_i[P_i]$ a
divisor of $C$ which is an effective Cartier
divisor (e.g. all $n_i\ge0$). Then the module

$$
\mathcal{O}_C(D)
$$

of [def-sc-divisor] (a sub-$\mathcal{O}_C$-module of the constant sheaf
$k(C)$) and the module $\mathcal{O}_C(D)$ of
[def-pc-divisor-line-bundle] are canonically isomorphic.

## Proof

Every local ring $\mathcal{O}_{C,P}$ at a closed point is regular of
dimension one ([lem-sc-smooth-regular]), hence a discrete valuation
ring ([lem-sc-regular-dim1-dvr]); in particular $C$ is normal, and being
connected it is integral. For $n_i\ge0$ the divisor $D$ is the
effective Cartier divisor ([def-sc-effective-cartier-divisor]) whose
ideal $\mathcal{I}_D$ is generated near $P_i$ by $t_i^{n_i}$, with $t_i$ a
uniformizer at $P_i$, and is trivial away from the $P_i$
([lem-sc-point-cartier]).

Cover $C$ by opens $U$ on which $\mathcal{I}_D=f\mathcal{O}_U$ for some
$f\in k(C)^*$ (take $f=t_i^{n_i}$ near $P_i$, with $U$ containing no
other $P_j$, and $f=1$ on $C\setminus\{P_1,\ldots,P_m\}$); then
$\operatorname{div}(f)|_U=D|_U$. Since $f$ is a non-zero-divisor, a
homomorphism $\mathcal{I}_D|_U\to\mathcal{O}_U$ is determined by the image $a$ of
$f$, and $a\mapsto a/f$ identifies
$\mathcal{H}om(\mathcal{I}_D,\mathcal{O}_C)|_U=\mathcal{I}_D^\vee|_U$ with the submodule
$f^{-1}\mathcal{O}_U$ of $k(C)$; these identifications glue to an embedding
$\mathcal{I}_D^\vee\hookrightarrow k(C)$ with image
$\{g:g\,\mathcal{I}_D\subseteq\mathcal{O}_C\}$. On the other hand, for $V\subseteq U$
open, $g\in k(C)$ satisfies
$\operatorname{div}(g)|_V+D|_V\ge0$ iff $v_P(gf)\ge0$ for all closed
$P\in V$, iff $gf\in\bigcap_{P\in V}\mathcal{O}_{C,P}=\mathcal{O}_C(V)$ (the integral
scheme $V$ has the intersection of its local rings as ring of
functions, and its non-closed point is the generic point). So the module
of [def-sc-divisor] is also $f^{-1}\mathcal{O}_U$ on $U$. The two
subsheaves of $k(C)$ agree on a cover, hence coincide, which gives the
canonical isomorphism.
