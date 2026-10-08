+++
id = "lem-pur-a1-direct-image"
kind = "lemma"
title = "The affine line has no higher direct images"
order = 1934
uses = ["def-pur-conventions", "def-weil-derived-direct-image", "fix-prop-adjunctions", "lem-weil-derived-direct-image-composition", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-comparison-direct-image", "prop-weil-pbc-strict-henselization-stalk-formula", "sbc-def-base-change-map", "sbc-lem-strict-henselian-constant-cohomology", "sbc-thm-smooth-base-change", "thm-pur-kummer-affine-line", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $B$ be a separated
finite-type $k$-scheme and let $\pi:\mathbf A^1_B\to B$ be the
projection, with the adjunction $L\pi^*\dashv R\pi_*$ and unit
$\eta_\pi$ of [fix-prop-adjunctions]. Then

$$
\eta_\pi(\Lambda_B):\quad
\Lambda_B\xrightarrow{\ \sim\ }R\pi_*\Lambda_{\mathbf A^1_B}
$$

is an isomorphism: the affine line has no higher direct images for the
constant coefficients, and its $H^0$ is the unit.

## Proof

We argue on the small etale site and transport at the end. The base
field $k$ of [def-pur-conventions] is algebraically closed, and
$\Lambda=A$ is finite with $\ell^NA=0$ for some $N$, $\ell\neq p$.

Step 1: stalks. Let $\bar b$ be a geometric point of $B$ and let
$S'=B_{(\bar b)}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{B,\bar b}$
be the strict henselization. Since $\pi$ is quasi-compact and
quasi-separated and $\mathbf A^1_B\times_BS'=\mathbf A^1_{S'}$, the
stalk formula [prop-weil-pbc-strict-henselization-stalk-formula] gives
$$
(R\pi_*\Lambda_{\mathbf A^1_B})_{\bar b}\simeq
R\Gamma(\mathbf A^1_{S'},\Lambda),
$$
and under it the stalk of $\eta_\pi(\Lambda_B)$ is the pullback
$\Lambda=\Gamma(S',\Lambda)\to R\Gamma(\mathbf A^1_{S'},\Lambda)$ along
the projection $e:\mathbf A^1_{S'}\to S'$.

Step 2: smooth base change to the geometric affine line. The scheme
$S'$ is a $k$-scheme, and $\mathbf A^1_{S'}=\mathbf A^1_k\times_kS'$.
Apply the smooth base change theorem [sbc-thm-smooth-base-change] to
the cartesian square with smooth side $f:\mathbf A^1_k\to\operatorname{Spec}k$,
quasi-compact quasi-separated side $g:S'\to\operatorname{Spec}k$
(affine), and the projections $h:\mathbf A^1_{S'}\to\mathbf A^1_k$,
$e:\mathbf A^1_{S'}\to S'$, and to the constant sheaf $\Lambda$ on
$S'$ (torsion of order prime to $p$): the base-change maps of
[sbc-def-base-change-map]
$$
f^{-1}R^qg_*\Lambda\xrightarrow{\ \sim\ }R^qh_*\Lambda
$$
are isomorphisms for all $q$. As $k$ is algebraically closed, $R^qg_*\Lambda$ is the
constant sheaf $H^q(S',\Lambda)$ on $\operatorname{Spec}k$, which is $\Lambda$
for $q=0$ and $0$ for $q>0$ because $S'$ is strictly henselian
([sbc-lem-strict-henselian-constant-cohomology]). Hence the map
$\Lambda_{\mathbf A^1_k}\to Rh_*\Lambda_{\mathbf A^1_{S'}}$ adjoint to
the pullback along $h$ is an isomorphism, and by the composition of derived direct images
[lem-weil-derived-direct-image-composition] (item (5)) the pullback
$$
h^*:R\Gamma(\mathbf A^1_k,\Lambda)\xrightarrow{\ \sim\ }
R\Gamma(\mathbf A^1_{S'},\Lambda)
$$
is an isomorphism.

Step 3: the geometric fibre. By [thm-pur-kummer-affine-line](1) (with
trivial twist: over the algebraically closed field $k$ a primitive
$\ell^N$-th root of unity trivializes $\mu_{\ell^N}$, so the
statement for $\Lambda(1)$ is the statement for $\Lambda$),
$H^q(\mathbf A^1_k,\Lambda)=0$ for $q>0$ and $H^0(\mathbf A^1_k,\Lambda)=\Lambda$,
the constants. With Steps 1–2, $(R^q\pi_*\Lambda)_{\bar b}=0$ for
$q>0$ and the stalk of $\eta_\pi(\Lambda_B)$ in degree $0$ is the
isomorphism of $\Lambda$ onto the constants of
$H^0(\mathbf A^1_{S'},\Lambda)$ (the constants of $\mathbf A^1_k$ pull
back to the constants). Since geometric stalks are conservative
([lemma-weil-pbc-geometric-stalk-conservative]), applied to the
cohomology sheaves, $\eta_\pi(\Lambda_B)$ is an isomorphism on the
etale site.

Step 4: transport. The unit of [fix-prop-adjunctions] on the
pro-etale site is the image of the etale unit under the comparison
functor: by [prop-weil-pbc-comparison-direct-image] the comparison
inverse image commutes with the derived direct image of
[def-weil-derived-direct-image], and it is fully faithful on
bounded-below complexes by [thm-weil-pbc-site-comparison]. Hence the
pro-etale unit $\eta_\pi(\Lambda_B)$ is an isomorphism as well.
