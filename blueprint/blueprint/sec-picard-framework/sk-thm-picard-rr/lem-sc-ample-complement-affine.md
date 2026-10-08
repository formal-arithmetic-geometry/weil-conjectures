+++
id = "lem-sc-ample-complement-affine"
kind = "lemma"
title = "Complements of ample divisors are affine"
order = 714
uses = ["def-sc-ample", "def-sc-divisor", "def-sc-effective-cartier-divisor"]
+++
Let $X$ be a proper scheme over a field $k$, $D\subseteq X$ an
effective Cartier divisor ([def-sc-effective-cartier-divisor])
and $\mathcal L:=\mathcal O_X(D)$
ample. Then $X\setminus D$ is affine.

## Proof

Choose $m\geq1$ with $\mathcal L^{\otimes m}$ very ample
([def-sc-ample]) and let $i:X\hookrightarrow\mathbf P^N_k$ be
the closed immersion given by the complete linear system
$|\mathcal L^{\otimes m}|$, so that
$i^*\mathcal O(1)\cong\mathcal L^{\otimes m}$ and every global
section of $\mathcal L^{\otimes m}$ is pulled back from a linear
form on $\mathbf P^N$. Let $s=1_D\in H^0(X,\mathcal L)$ be the
canonical section, with $V(s)=D$; then
$s^{\otimes m}\in H^0(X,\mathcal L^{\otimes m})$ has zero locus
$D$, and there is a linear form $\ell$ on $\mathbf P^N$ with
$i^*\ell=s^{\otimes m}$. For the hyperplane
$H:=V(\ell)\subset\mathbf P^N$ one has
$i^{-1}(H)=V(s^{\otimes m})=D$, so

$$
i(X\setminus D)=i(X)\cap(\mathbf P^N\setminus H).
$$

The complement of a hyperplane is affine space,
$\mathbf A^N_k\cong\mathbf P^N_k\setminus H$, and
$i(X)\cap\mathbf A^N$ is closed in $\mathbf A^N$, hence affine
(a closed immersion is an affine morphism: *reference:
Stacks Project, Morphisms of Schemes: closed immersions are
affine*); therefore $X\setminus D$ is affine.
