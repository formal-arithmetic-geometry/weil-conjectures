+++
id = "lem-pur-gysin-structure"
kind = "lemma"
title = "Structure of the exceptional inverse image of the zero section"
order = 1946
uses = ["def-pur-affine-line-datum", "def-pur-conventions", "def-weil-derived-direct-image", "def-weil-exceptional-inverse-image", "fix-prop-adjunctions", "lem-amb-cartier-kummer-map", "lem-amb-closed-support-hom", "lem-pur-support-localization-triangle", "lem-weil-derived-direct-image-composition", "prop-pur-gm-relative-kummer", "thm-pur-with-support-exactness"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
explicit ingredients, let $\Lambda=A$, and let
$s:Y\hookrightarrow\mathbf A^1_Y$ be the zero section. Then:

1. The object $Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]$ lies in
$D^b_{ctf}(Y,\Lambda)$ and is concentrated in degree zero after the
displayed shift, with lisse rank-one cohomology sheaf.
1. Under the long exact sequence of
[thm-pur-with-support-exactness] for the pair
$(s(Y),\mathbf A^1_Y)$, there is a canonical identification
$$
\Gamma\!\left(Y,\mathcal H^0\bigl(Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]\bigr)\right)
\cong H^2_{s(Y)}\bigl(\mathbf A^1_Y,\Lambda(1)\bigr),
$$
via which the boundary of the
Kummer class of $t$ corresponds
to an element of the space of morphisms
$$
\operatorname{Hom}_{D(Y,\Lambda)}\bigl(\Lambda_Y,Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]\bigr).
$$

(Source: the Gysin sequence of the zero section, i.e. the
affine-line case of the fundamental exact sequence of cohomological
purity – Milne, Lectures on Etale Cohomology, Section 16, Theorems
16.1 and 16.7, and Proposition 16.11 (the case $r=2c-1=1$).)

## Proof

Write $p:\mathbf A^1_Y\to Y$, $j:\mathbf G_{m,Y}\hookrightarrow\mathbf A^1_Y$
and $\pi=pj$ as in [def-pur-affine-line-datum]. Apply the localization
triangle of [lem-pur-support-localization-triangle] for the closed–open
pair $(s,j)$ and $K=\Lambda(1)_{\mathbf A^1_Y}$, whose first term is
built from the exceptional inverse image of
[def-weil-exceptional-inverse-image],
$$
s_*Rs^!\Lambda(1)\longrightarrow\Lambda(1)\longrightarrow
Rj_*j^*\Lambda(1)\xrightarrow{+1},
$$
and then the triangulated functor $Rp_*$ of
[def-weil-derived-direct-image]. Since $s_*$ is exact,
$Rp_*s_*=R(ps)_*=\operatorname{id}$, and $Rp_*Rj_*=R\pi_*$ by the
composition of derived direct images
[lem-weil-derived-direct-image-composition], this gives a
distinguished triangle on $Y$
$$
Rs^!\Lambda(1)\longrightarrow Rp_*\Lambda(1)\xrightarrow{\ j^*\ }
R\pi_*\Lambda(1)\xrightarrow{\ \delta\ }Rs^!\Lambda(1)[1].
$$
By [prop-pur-gm-relative-kummer](1) the middle term is $\Lambda_Y(1)$ in
degree $0$, via the unit of $p$. By [prop-pur-gm-relative-kummer](2),(3)
the right-hand term has $\mathcal H^0=\Lambda_Y(1)$ via the unit of
$\pi$, $\mathcal H^1$ free of rank one on $\kappa(t)$, and no other
cohomology sheaves. By [fix-prop-adjunctions](3) the unit of $\pi$ is
$j^*$ composed with the unit of $p$, so $\mathcal H^0(j^*)$ is an
isomorphism. The long exact sequence of cohomology sheaves
$$
0\to\mathcal H^0(Rs^!\Lambda(1))\to R^0p_*\Lambda(1)\xrightarrow{\sim}
R^0\pi_*\Lambda(1)\to\mathcal H^1(Rs^!\Lambda(1))\to R^1p_*\Lambda(1)=0
\to R^1\pi_*\Lambda(1)\xrightarrow{\ \delta\ }\mathcal H^2(Rs^!\Lambda(1))
\to R^2p_*\Lambda(1)=0\to\cdots
$$
therefore gives $\mathcal H^m(Rs^!\Lambda(1))=0$ for $m\neq2$ (for
$m\geq3$ it sits between $R^{m-1}\pi_*\Lambda(1)=0$ and
$R^mp_*\Lambda(1)=0$), and an isomorphism
$$
\delta:\ \Lambda_Y\cdot\kappa(t)=R^1\pi_*\Lambda(1)\xrightarrow{\ \sim\ }
\mathcal H^2(Rs^!\Lambda(1))=\mathcal H^0\bigl(Rs^!\Lambda(1)[2]\bigr).
$$
So $Rs^!\Lambda_{\mathbf A^1_Y}(1)[2]$ is concentrated in degree zero,
with cohomology sheaf the constant sheaf $\Lambda_Y$, free of rank one on
the boundary $\delta\kappa(t)$; in particular it is lisse of rank one,
constructible, and of finite Tor amplitude, i.e. it lies in
$D^b_{ctf}(Y,\Lambda)$. Constancy is read off from the triangle; it is
not inferred from constancy of ranks.

For the second assertion, the support identification
[lem-amb-closed-support-hom] identifies
$H^2_{s(Y)}(\mathbf A^1_Y,\Lambda(1))$ with
$\operatorname{Hom}_Y(\Lambda_Y,Rs^!\Lambda(1)[2])$.
Since the target is concentrated in degree zero, this Hom group is
$\Gamma(Y,\mathcal H^0(Rs^!\Lambda(1)[2]))$.
The boundary of the coordinate class in
[def-pur-affine-line-datum], [thm-pur-with-support-exactness]
is precisely the supported Cartier morphism of
[lem-amb-cartier-kummer-map]; the latter construction also gives
its compatibility with base change of this zero-section pair.
