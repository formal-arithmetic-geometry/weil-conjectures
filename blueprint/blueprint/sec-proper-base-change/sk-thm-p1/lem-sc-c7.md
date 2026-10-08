+++
id = "lem-sc-c7"
kind = "lemma"
title = "C7: invariance on proper curves"
order = 1118
uses = ["def-sc-curves", "def-sc-field-extension", "def-weil-pbc-eight-curve-assertions", "lem-sc-artin-schreier-dimension", "lem-sc-artin-schreier-k", "lem-sc-as-sequence", "lem-sc-base-change-curve", "lem-sc-flat-base-change-coherent", "lem-sc-frobenius-fixed-invariance", "lem-sc-morphism-from-function", "lem-sc-proper-affine-finite", "thm-sc-constant-invariance"]
+++
Let $k\subseteq k'$ be algebraically closed, let $C$ be a
smooth proper connected curve over $k$, and let
$r$ be a prime. Then the constant sheaf $\mathbf F_r$ satisfies
$\mathcal C_7(C,\mathbf F_r)$ of
[def-weil-pbc-eight-curve-assertions]: the pullback maps
$\rho^q_{k'/k}(C,\mathbf F_r)$ are isomorphisms for every $q\geq0$.

## Proof

If $r\neq\operatorname{char}k$, this is the proper case of
[thm-sc-constant-invariance]. If
$r=\operatorname{char}k=p>0$, then $H^q(C,\mathbf F_p)=0$ for
$q>1$ and the same holds over $k'$ (since $C_{k'}$ is a smooth
proper connected curve over $k'$ by [lem-sc-base-change-curve] and
[lem-sc-artin-schreier-dimension]), and
$H^0(C,\mathbf F_p)=\mathbf F_p=H^0(C_{k'},\mathbf F_p)$. It
remains to treat $q=1$, where we argue directly. The
Artin–Schreier sequence ([lem-sc-as-sequence]) gives the long
exact sequence

$$
0\to H^0(C,\mathbf F_p)\to H^0(C,\mathcal O_C)\xrightarrow{\wp}
H^0(C,\mathcal O_C)\to H^1(C,\mathbf F_p)\to H^1(C,\mathcal O_C)
\xrightarrow{\wp}H^1(C,\mathcal O_C)\to\cdots.
$$

Now $H^0(C,\mathcal O_C)=k$: a global function $f\in H^0(C,\mathcal O_C)\setminus k$ would, by
[lem-sc-morphism-from-function], define a morphism
$C\to\mathbf A^1_k$ whose image is proper (the image of a proper
scheme in a separated finite-type target is proper) and affine,
hence finite by [lem-sc-proper-affine-finite]; but $C$ is
connected, so the image is a single point and $f$ is constant.
Since $\wp:k\to k$ is surjective
([lem-sc-artin-schreier-k]), the exact sequence gives

$$
H^1(C,\mathbf F_p)\cong\ker\bigl(\wp:H^1(C,\mathcal O_C)\to
H^1(C,\mathcal O_C)\bigr).
$$

The map $\wp$ on $H^1(C,\mathcal O_C)$ is $F-1$, where $F$
is the $p$-linear endomorphism induced by $f\mapsto f^p$ (on
Cech cocycles, $(g_{ij})\mapsto(g_{ij}^p)$ is $p$-linear).
Likewise, over $k'$, $H^1(C_{k'},\mathbf F_p)\cong\ker(F'-1)$
for the base-changed map $F'$ on
$H^1(C_{k'},\mathcal O_{C_{k'}})$. By
[lem-sc-flat-base-change-coherent],
$H^1(C_{k'},\mathcal O_{C_{k'}})\cong H^1(C,\mathcal O_C)\otimes_kk'$, compatibly with Frobenius (the
Cech computation is functorial in the base field), so
$F'=F\otimes\sigma_{k'}$, and the pullback map
$H^1(C,\mathbf F_p)\to H^1(C_{k'},\mathbf F_p)$ is the natural map
of fixed points $V^F\to(V\otimes_kk')^{F'}$. By
[lem-sc-frobenius-fixed-invariance] this map is an
isomorphism.
