+++
id = "thm-pur-regular-immersion-purity"
kind = "theorem"
title = "Purity for regular closed immersions"
order = 2034
uses = ["cor-pur-affine-space-purity", "cor-pur-affine-space-zero-section-purity", "lem-pur-projection-purity-agreement", "def-coefficient-twists-detailed", "def-pur-conventions", "def-pur-frame-class", "def-pur-regular-immersion", "def-weil-derived-tensor", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-frame-independence", "lem-pur-immersion-twist", "lem-pur-kunneth-supported", "lem-pur-regular-immersion-linearization", "lem-pur-regular-immersion-smooth-structure", "thm-pur-composition-coherence", "thm-pur-diagonal-dualizing-object"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $i:Z\hookrightarrow X$ be a
regular closed immersion of pure
codimension $c$, with $X$ smooth over the perfect field $k$ and
$Z$ regular. Then $Ri^!\Lambda_X(c)[2c]$ is concentrated in degree
$0$, with $\mathcal H^0$ free of rank one, so that
$H^0(Z,Ri^!\Lambda_X(c)[2c])=H^{2c}_Z(X,\Lambda(c))$. The
*fundamental class*
$[Z\subset X]\in H^{2c}_Z(X,\Lambda(c))$ is the global class whose
restriction to every frame $(U,f)$ of [def-pur-frame-class] is
$\operatorname{cl}(f)$ (it exists and is unique by
[lem-pur-frame-independence] and the sheaf property of
$\mathcal H^0$). There is a canonical isomorphism

$$
\operatorname{cl}_i:\Lambda_Z\xrightarrow{\ \sim\ }Ri^!\Lambda_X(c)[2c],
\qquad 1\longmapsto[Z\subset X],
$$

equivalently (cancelling the invertible twist) a canonical
isomorphism $Ri^!\Lambda_X\xrightarrow{\sim}\Lambda_Z(-c)[-2c]$,
the inverse of $\operatorname{cl}_i(-c)[-2c]$. It is compatible with
etale base change and with exterior products.

## Proof

Cancellation of the Tate factor uses the invertibility and twist identifications of [def-coefficient-twists-detailed].
Step 1: the $\omega$-identification. Work on each open-and-closed
connected component of $X$; the resulting isomorphisms assemble
over their disjoint union. By
[lem-pur-regular-immersion-smooth-structure], $a_X$ and $a_Z$
are smooth of dimensions $n$ and $m=n-c$, and
$a_Z=a_X\circ i$. The composition law for the exceptional inverse
image ([def-weil-exceptional-inverse-image]) gives

$$
\omega_{Z/k}=Ra_Z^!\Lambda_k
\;\cong\;Ri^!\bigl(Ra_X^!\Lambda_k\bigr)
=Ri^!\omega_{X/k},
$$

and by the smooth purity of the structure morphisms
([thm-pur-diagonal-dualizing-object] applied to $a_X$ and
$a_Z$),

$$
\omega_{X/k}\;\cong\;\Lambda_X(n)[2n],
\qquad
\omega_{Z/k}\;\cong\;\Lambda_Z(m)[2m].
$$

Step 2: the co-projection removes the twist. By
[lem-pur-immersion-twist] (with $K=\Lambda_X$ and $m=n$),

$$
Ri^!\Lambda_X(n)[2n]
\;\cong\;\bigl(Ri^!\Lambda_X\bigr)\otimes^L_{\Lambda_Z}\Lambda_Z(n)[2n].
$$

Combined with Step 1 and the cancellation of the invertible
$\Lambda_Z(n)[2n]$ (in the monoid of invertible objects of
[def-weil-derived-tensor]):

$$
Ri^!\Lambda_X
\;\cong\;\Lambda_Z(m-n)[2m-2n]
=\Lambda_Z(-c)[-2c].
$$

Step 3: the class. Twisting the identification of Steps 1–2 by
$(c)[2c]$ ([lem-pur-immersion-twist]) gives a canonical isomorphism
$\Phi:\Lambda_Z\xrightarrow{\sim}Ri^!\Lambda_X(c)[2c]$; in particular
$Ri^!\Lambda_X(c)[2c]$ is concentrated in degree $0$ with $\mathcal H^0$
free of rank one, and $H^0(Z,Ri^!\Lambda_X(c)[2c])=H^{2c}_Z(X,\Lambda(c))$
since $Ri_*Ri^!$ is the derived functor of sections with support in $Z$.
It carries the canonical generator of $\Lambda_Z$ to a class
$\Phi(1)\in H^{2c}_Z(X,\Lambda(c))$; we show that $\Phi(1)$ is the
fundamental class $[Z\subset X]$ glued from the frame classes of
[def-pur-frame-class]. By
[lem-pur-regular-immersion-linearization], etale-locally the pair
$(X,Z)$ is the linear pair $(\mathbf A^{c+m}_k,\mathbf A^m_k)$; on
the model, the structure-morphism identifications of Step 1 are the
affine-space purity comparisons of [cor-pur-affine-space-purity]
for the projections (the smooth purity map of a projection agrees with
the affine-space comparison by [lem-pur-projection-purity-agreement]),
so $\Phi$ for the linear immersion $i_0$ is the inverse of $Ri_0^!$ of
the affine-space comparison $\gamma_{p,\Lambda}$ for the projection
$p$ with $p\,i_0=\operatorname{id}$, composed with
$Ri_0^!Rp^!\cong\operatorname{id}$; by
[cor-pur-affine-space-zero-section-purity] this is the zero-section
isomorphism normalized by the product of the Kummer boundaries of the
coordinates, hence the composite identification carries $1$
to the $c$-fold exterior product of the rank-one Kummer boundaries of
the coordinates, i.e. to the class
$\operatorname{cl}(f)=\partial_1\kappa(f_1)\cup\cdots\cup\partial_c\kappa(f_c)$
of the standard frame, by [lem-pur-kunneth-supported] and
[lem-pur-frame-independence] (the frame class depends only on the
pair; the identification of Steps 1–2 is compatible with the
etale coordinate map $u:U\to\mathbf A^{c+m}_k$ and its restriction
$u':V\to\mathbf A^m_k$ because $a_U=a_{\mathbf A^{c+m}}\circ u$ and
$a_V=a_{\mathbf A^m}\circ u'$ with $u,u'$ etale, by the composition
compatibility [thm-pur-composition-coherence], while
$Ri_V^!u^*=u'^*Ri_0^!$ for the linear immersion $i_0$; and
Kummer classes, boundaries and supported cup products commute with
$u^*$, which carries the coordinates $x_j$ to the frame $f_j$). Hence
the two global classes agree: by Steps 1–2,
$Ri^!\Lambda_X(c)[2c]$ is concentrated in degree $0$, so both are
global sections of the single sheaf $\mathcal H^0$, they agree on
the linear neighbourhoods, which cover $Z$, and sections of a sheaf
agreeing on a cover agree. Since the identification of Steps 1–2 is
an isomorphism, its value $\Phi(1)=[Z\subset X]$ at $1$ generates every
stalk, and the identification is $\operatorname{cl}_i$.

Step 4: the compatibilities. The canonical identification is the
composite of the smooth-purity identifications of the two structure
morphisms, the composition law for $(-)^!$, and the co-projection;
each of these is compatible with etale base change and with the
exterior-product (Künneth) structure by the corresponding
compatibilities of [thm-pur-diagonal-dualizing-object] and
[lem-pur-kunneth-supported], and the class of Step 3 is
compatible with them by [lem-pur-frame-independence].
