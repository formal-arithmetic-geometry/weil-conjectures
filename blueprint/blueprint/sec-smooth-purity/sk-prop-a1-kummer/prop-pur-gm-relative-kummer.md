+++
id = "prop-pur-gm-relative-kummer"
kind = "theorem"
tags = ["latex:proposition"]
title = "The affine line and the punctured line over a base"
order = 1935
uses = ["def-coefficient-twists-detailed", "def-pur-affine-line-datum", "def-pur-conventions", "def-weil-derived-cohomology-sheaves", "def-weil-derived-direct-image", "fix-prop-adjunctions", "lem-pur-a1-direct-image", "lem-pur-finite-kummer-level", "lem-weil-derived-direct-image-composition", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-comparison-direct-image", "prop-weil-pbc-strict-henselization-stalk-formula", "sbc-lem-strict-henselian-constant-cohomology", "sbc-thm-smooth-base-change", "thm-pur-kummer-affine-line", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $\Lambda=A=A_{E,n}$, let $Y$ be a separated finite-type $k$-scheme,
and use the affine-line datum of [def-pur-affine-line-datum]: the
projection $p:\mathbf A^1_Y\to Y$, the zero section $s$, the open
complement $j:\mathbf G_{m,Y}\hookrightarrow\mathbf A^1_Y$, the composite
$\pi=pj:\mathbf G_{m,Y}\to Y$, the finite-level twist
$\Lambda(1)=\mu_{\ell^N}\otimes_{\mathbf Z/\ell^N}A$, and the Kummer class
$\kappa(t)\in H^1(\mathbf G_{m,Y},\Lambda(1))$ of the coordinate. Write
$R^m\pi_*=\mathcal H^m R\pi_*$ for the cohomology sheaves of
[def-weil-derived-cohomology-sheaves]. Then:

1. *(Acyclicity of the affine line.)* The units
$\Lambda_Y\to Rp_*\Lambda_{\mathbf A^1_Y}$ and
$\Lambda_Y(1)\to Rp_*\Lambda_{\mathbf A^1_Y}(1)$ are isomorphisms; so
$R^mp_*\Lambda(1)=0$ for $m>0$.
1. *(The Kummer generator.)* The unit
$\Lambda_Y(1)\to R^0\pi_*\Lambda(1)$ — equivalently, restriction along $j$
composed with the pullback $p^*$ — is an isomorphism, and the map
$$
\Lambda_Y\longrightarrow R^1\pi_*\Lambda(1),\qquad 1\longmapsto\kappa(t),
$$
sending $1$ to the image of $\kappa(t)$ under the edge map
$H^1(\mathbf G_{m,Y},\Lambda(1))=H^1(Y,R\pi_*\Lambda(1))\to
\Gamma(Y,R^1\pi_*\Lambda(1))$, is an isomorphism: $R^1\pi_*\Lambda(1)$
is free of rank one on $\kappa(t)$.
1. *(Vanishing above degree one.)* $R^m\pi_*\Lambda(1)=0$ for $m\geq2$.
1. *(Base change.)* For every morphism $g:Y'\to Y$ of separated
finite-type $k$-schemes, with base changes
$p':\mathbf A^1_{Y'}\to Y'$, $\pi':\mathbf G_{m,Y'}\to Y'$ and
$g':\mathbf G_{m,Y'}\to\mathbf G_{m,Y}$, the pullback of the Kummer class
is the Kummer class, $g'^*\kappa(t)=\kappa(t')$, and the base-change
morphisms
$$
g^*Rp_*\Lambda(1)\to Rp'_*\Lambda(1),\qquad
g^*R\pi_*\Lambda(1)\to R\pi'_*\Lambda(1)
$$
are isomorphisms.

In particular, taking $Y'=\bar y$ a geometric point, (1)–(3) are
equivalent to the corresponding statements for $\mathbf A^1$ and
$\mathbf G_m$ over an algebraically closed field, which are
[thm-pur-kummer-affine-line].

## Proof

We follow the reduction to a geometric fibre by smooth base change;
nothing below uses the exceptional inverse image of the zero section.
Throughout, $\Lambda(1)_{\mathbf A^1_Y}=p^*\Lambda_Y(1)$ and
$\Lambda(1)_{\mathbf G_{m,Y}}=\pi^*\Lambda_Y(1)$, since $\mu_{\ell^N}$ and
the coefficient extension by $A$ are compatible with pullback
([lem-pur-finite-kummer-level], [def-coefficient-twists-detailed]).
Since the base field $k$ of [def-pur-conventions] is algebraically
closed, a primitive $\ell^N$-th root of unity $\zeta\in k$ trivializes
$\mu_{\ell^N}$, hence $\Lambda(1)\cong\Lambda$, on every $k$-scheme,
compatibly with pullback. We compute on the small etale site; the
comparison inverse image commutes with the derived direct images of
[def-weil-derived-direct-image] ([prop-weil-pbc-comparison-direct-image])
and is fully faithful on bounded-below complexes
([thm-weil-pbc-site-comparison]), so the units, the classes and the
isomorphisms below transport to the pro-etale site.

Step 1: clause (1). The untwisted statement is
[lem-pur-a1-direct-image] with $B=Y$. Under the trivialization by
$\zeta$ the twisted unit $\Lambda_Y(1)\to Rp_*p^*\Lambda_Y(1)$ of
[fix-prop-adjunctions] is the untwisted unit
$\Lambda_Y\to Rp_*\Lambda_{\mathbf A^1_Y}$, hence an isomorphism; so
$R^mp_*\Lambda(1)=0$ for $m>0$.

Step 2: clauses (2) and (3), on stalks. Let $\bar y$ be a geometric
point of $Y$ and $S'=Y_{(\bar y)}$ the strict henselization, a
$k$-scheme. As $\pi$ is quasi-compact and quasi-separated and
$\mathbf G_{m,Y}\times_YS'=\mathbf G_{m,S'}$, the stalk formula
[prop-weil-pbc-strict-henselization-stalk-formula] gives
$$
(R\pi_*\Lambda(1))_{\bar y}\simeq R\Gamma(\mathbf G_{m,S'},\Lambda(1)),
$$
compatibly with the unit (on the left) and pullback of constants along
$e:\mathbf G_{m,S'}\to S'$ (on the right), and compatibly with global
classes: the stalk at $\bar y$ of the section of
$R^1\pi_*\Lambda(1)$ defined by a class in
$H^1(\mathbf G_{m,Y},\Lambda(1))$ is its restriction to
$\mathbf G_{m,S'}$.
Now $\mathbf G_{m,S'}=\mathbf G_{m,k}\times_kS'$. The smooth base change
theorem [sbc-thm-smooth-base-change], for the square with smooth side
$f:\mathbf G_{m,k}\to\operatorname{Spec}k$, affine side
$g:S'\to\operatorname{Spec}k$, projections
$h:\mathbf G_{m,S'}\to\mathbf G_{m,k}$ and $e$, and the constant sheaf
$\Lambda(1)_{S'}$ (torsion prime to $p$), gives
$f^{-1}R^qg_*\Lambda(1)\cong R^qh_*\Lambda(1)$ for all $q$. As $S'$ is
strictly henselian, $R^qg_*\Lambda(1)=H^q(S',\Lambda(1))$ is
$\Lambda(1)(k)$ for $q=0$ and $0$ for $q>0$
([sbc-lem-strict-henselian-constant-cohomology]); so
$\Lambda(1)_{\mathbf G_{m,k}}\to Rh_*\Lambda(1)_{\mathbf G_{m,S'}}$ is an
isomorphism and, by the composition of derived direct images
[lem-weil-derived-direct-image-composition] (item (5)), pullback along
$h$ is an isomorphism
$$
h^*:R\Gamma(\mathbf G_{m,k},\Lambda(1))\xrightarrow{\ \sim\ }
R\Gamma(\mathbf G_{m,S'},\Lambda(1)).
$$
By [thm-pur-kummer-affine-line](2),(3), the left side has $H^0=A$
(the constants), $H^1$ free of rank one on the Kummer class of the
coordinate of $\mathbf G_{m,k}$, and no other cohomology. The Kummer
boundary and the coefficient extension of [def-pur-affine-line-datum]
commute with pullback, and the coordinate $t$ restricts to the
coordinate on $\mathbf G_{m,S'}$ and on $\mathbf G_{m,k}$; so the
restriction of $\kappa(t)$ to $\mathbf G_{m,S'}$ is $h^*$ of the Kummer
class of the coordinate of $\mathbf G_{m,k}$. Consequently, at every
geometric point $\bar y$ (writing $R^m\pi_*$ for the cohomology
sheaves of [def-weil-derived-cohomology-sheaves]):
$(R^m\pi_*\Lambda(1))_{\bar y}=0$ for $m\geq2$; the stalk of the unit
$\Lambda_Y(1)\to R^0\pi_*\Lambda(1)$ is an isomorphism (constants go to
constants); and the stalk of $\Lambda_Y\to R^1\pi_*\Lambda(1)$,
$1\mapsto\kappa(t)$, sends $1$ to a generator of a free rank-one
module, hence is an isomorphism. Geometric stalks being conservative
([lemma-weil-pbc-geometric-stalk-conservative]), this proves (3) and both
halves of (2). By [fix-prop-adjunctions](3) the unit of $\pi=pj$ is
the unit of $p$ followed by $Rp_*$ of the unit of $j$, i.e. by
restriction along $j$; with Step 1 this identifies the unit
$\Lambda_Y(1)\to R^0\pi_*\Lambda(1)$ with restriction along $j$
composed with $p^*$, as stated.

Step 3: clause (4). The Kummer sequence of
[def-pur-affine-line-datum], its boundary map, and the coefficient
extension by $A$ are compatible with pullback along
$g':\mathbf G_{m,Y'}\to\mathbf G_{m,Y}$, and $g'^*t=t'$ is the coordinate
of $\mathbf G_{m,Y'}$; hence $g'^*\kappa(t)=\kappa(t')$. The base-change
morphism $g^*Rf_*\to Rf'_*g'^*$ (for $f\in\{p,\pi\}$) is the mate of the
equality $f'^*g^*=g'^*f^*$ under the adjunctions of
[fix-prop-adjunctions], and it is compatible with the units, i.e. its
composite with $g^*$ of the unit $\Lambda_Y(1)\to Rf_*\Lambda(1)$ is the
unit $\Lambda_{Y'}(1)\to Rf'_*\Lambda(1)$; it is also compatible with
pullback of cohomology classes, so on $\mathcal H^1$ for $f=\pi$ it
sends $g^*$ of the section $\kappa(t)$ to the section $g'^*\kappa(t)=
\kappa(t')$. By (1)–(3) over $Y$ and over $Y'$, both sides of each
base-change morphism have cohomology sheaves only in degrees $0$ (for
$p$) resp. $0$ and $1$ (for $\pi$); in degree $0$ they are
$\Lambda_{Y'}(1)$ via the units, and in degree $1$ they are free of rank
one on $g^*\kappa(t)$ resp. $\kappa(t')$. The morphism therefore induces
isomorphisms on all cohomology sheaves ($g^*$ being exact), and is an
isomorphism. For $Y'=\bar y$ a geometric point with algebraically closed
field, $Rf'_*$ is the cohomology of $\mathbf A^1_{\bar y}$ resp.
$\mathbf G_{m,\bar y}$, and the resulting stalk statements are exactly
those of [thm-pur-kummer-affine-line].
