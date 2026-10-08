+++
id = "rem-sf-fullcd-counterexample"
kind = "remark"
title = "The counterexample: a pro-étale base change whose comparison direct image has infinite cohomological dimension"
order = 2053
uses = ["def-sf-fullcd-used-class", "def-weil-full-cohomological-dimension", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site", "def-weil-pbc-site-comparison-morphism", "lem-sf-proetale-vanishing-detection", "prop-sf-comparison-bound-zero", "thm-sf-fullcd-used-class"]
+++
Fix an odd prime $\ell$, a finite extension $E/\Ql$, put
$A=A_{E,1}$ – a finite field of characteristic $\ell$ – fix a discrete set
$I$ of cardinality $\aleph_\omega$, and put

$$
S=\beta I\times\beta I,\qquad
U=\Spec\,\mathcal C_{\mathrm{lc}}(S,\mathbf C),\qquad
X_0=\Spec\mathbf C,
$$

where $\beta I$ is the Čech–Stone compactification of $I$ and
$\mathcal C_{\mathrm{lc}}(S,\mathbf C)$ is the ring of locally constant
$\mathbf C$-valued functions on $S$, so that $U$ is a scheme over
$X_0$. The seven clauses below are the construction and its computation.
The two sources used are Bhatt–Scholze,
[arXiv:1309.1198v2](https://arxiv.org/html/1309.1198v2), and
Bergfalk–Lambie-Hanson,
[arXiv:2412.19605v2](https://arxiv.org/html/2412.19605v2); their exact
statements, numbers and verbatim wording are recorded in Section 16.1 of the
audit ledger, the first at Lemmas 5.1.1 and 5.1.2, Corollary 5.1.6,
Definition 3.2.1, Example 4.1.10, Remark 4.1.11 and Proposition 4.2.8, the
second at Theorem 4.3, Lemma 4.8 and Theorem 4.11.

1. **(i)** *$U$ is an affine pro-étale object of $X_{0,\Proet}$, a
cofiltered limit of finite disjoint unions of points.* The profinite space
$S$ is the cofiltered limit of its finite quotients
$S\twoheadrightarrow S_i$, and
$\mathcal C_{\mathrm{lc}}(S,\mathbf C)=\colim_i\mathbf C^{S_i}$; hence
$$
U=\lim_i\Spec\bigl(\mathbf C^{S_i}\bigr)
=\lim_i\coprod_{S_i}\Spec\mathbf C
$$
is a cofiltered limit of finite disjoint unions of points with affine
transition maps, the structure maps $\Spec(\mathbf C^{S_i})\to X_0$ being
finite étale. Since a cofiltered limit of finite étale $X_0$-schemes is
pro-étale over $X_0$, the projection $U\to X_0$ is affine pro-étale and
$U$ is an object of the small pro-étale site
[def-weil-pbc-proetale-site].
1. **(ii)** *Its étale topos is the topos of sheaves on $S$, and
$\Gamma(U_{\Et},-)$ is exact.* Passing to small étale topoi along (i),
$$
\Mod(U_{\Et},A)\cong\Sh(S,A),
$$
the category of sheaves of $A$-modules on the profinite set $S$,
equivalently on the site of its finite quotients: an étale sheaf on
$\coprod_{S_i}\Spec\mathbf C$ is a family of $A$-modules indexed by the
finite set $S_i$, and the colimit of these categories along the cofiltered
system of quotients is $\Sh(S,A)$. Under this identification the global
sections of an étale sheaf on $U$ are computed on the finite quotients,
$H^q(U_{\Et},\mathcal G)=\colim_iH^q(S_i,\mathcal G_i)=0$ for $q>0$, a
finite set having no higher cohomology; so $\Gamma(U_{\Et},-)$ is an exact
functor on $\Sh(S,A)$.
1. **(iii)** *Weakly contractible objects of $U_{\Proet}$, and their
sections.* The weakly contractible objects of the pro-étale topos of
$\Spec\mathbf C$ correspond exactly to the extremally disconnected profinite
sets, evaluation on them is exact, and the topos is locally weakly
contractible (Bhatt–Scholze, Definition 3.2.1, Example 4.1.10, Remark 4.1.11
and Proposition 4.2.8); transported along the pro-étale morphism
$U\to X_0$, the objects
$$
U_T=\Spec\,\mathcal C_{\mathrm{lc}}(T,\mathbf C)\qquad
(T\ \text{extremally disconnected profinite})
$$
are weakly contractible and form a basis of $U_{\Proet}$, and on a weakly
contractible object every pro-étale cover has a section, so the global-sections
functor there is exact; this is the device of
[lem-sf-proetale-vanishing-detection], whose clause (ii) is the statement
that a complex of $A$-module sheaves on $U_{\Proet}$ is acyclic as soon as
its evaluations at the objects of such a basis are acyclic complexes.
1. **(iv)** *Unbounded $\operatorname{Ext}$ against the constant sheaf.*
By (ii) and by Bergfalk–Lambie-Hanson, Theorem 4.3, applied to the two
étale-origin factors $S=T=\beta I$ of cardinality $|I|=\aleph_\omega$ and
to the field $K=A$, the constant sheaf $A$ on the product
$\beta I\times\beta I=S$ has infinite injective dimension in
$\Sh(S,A)$:
$$
\operatorname{injdim}_{\Sh(S,A)}(A)=\infty .
$$
(For the *finite* field $A$ the first clause of the same theorem, proved
separately as Lemma 4.8, gives at the same time that the constant sheaf $A$
on an extremally disconnected compact Hausdorff space is injective.) Hence
for every integer $M$ there are a sheaf $G$ of $A$-modules on
$U_{\Et}$, that is, an object of $\Sh(S,A)$, and an integer $q>M$ with
$$
\operatorname{Ext}^q_{\Sh(S,A)}(G,A)\neq0 :
$$
otherwise $\operatorname{Ext}^q(-,A)=0$ for all $q>M$ would present $A$
as an object of injective dimension at most $M$.
1. **(v)** *The sheaf $F_G$, and the vanishing of its higher derived
Hom.* Put
$$
F_G=\mathcal H om_A\bigl(\nu_U^*G,A\bigr),
$$
a sheaf of $A$-modules on $U_{\Proet}$ in the sense of
[def-weil-pbc-proetale-modules], and outside the blueprint's coefficient
class unless $G$ is constructible. Then
$$
R\mathcal H om_A\bigl(\nu_U^*G,A\bigr)\cong
\mathcal H om_A\bigl(\nu_U^*G,A\bigr),
$$
that is, the derived Hom is concentrated in degree $0$. Indeed, at the
basis objects $U_T$ of (iii) the restriction of $\nu_U^*G$ is the constant
sheaf with value $G(T)$, sections there are exact by (iii), and the constant
sheaf $A$ is injective on $U_T$ by the injectivity clause of (iv); so
$\operatorname{Ext}^q_A\bigl(\nu_U^*G(U_T),A\bigr)=0$ for every $q>0$ and
every basis object, and therefore
$\mathcal E xt^q_A(\nu_U^*G,A)=0$ for $q>0$, by the detection criterion
[lem-sf-proetale-vanishing-detection](ii).
1. **(vi)** *$R\Gamma(U_{\Proet},F_G)=R\Hom_{\Sh(S,A)}(G,A)$, and the
failure of the bound.* From (v) and the identification of global sections of
the sheafified Hom with the derived Hom in the derived category of
$U_{\Proet}$,
$$
R\Gamma(U_{\Proet},F_G)
=R\Hom_{D(U_{\Proet},A)}\bigl(\nu_U^*G,A\bigr)
=R\Hom_{D(U_{\Et},A)}\bigl(G,R\nu_{U,*}A\bigr)
=R\Hom_{\Sh(S,A)}(G,A),
$$
the second step being the adjunction $\nu_U^*\dashv R\nu_{U,*}$ for the
comparison morphism of [def-weil-pbc-site-comparison-morphism] and the
third the identity $R\nu_{U,*}A=A$, which is
[prop-sf-comparison-bound-zero] applied to the constant étale sheaf
$A$. By the exactness of $\Gamma(U_{\Et},-)$ established in (ii), the
Leray spectral sequence of the composite
$\Gamma(U_{\Proet},-)=\Gamma(U_{\Et},-)\circ\nu_{U,*}$ degenerates and gives,
for every $q$,
$$
\Gamma\bigl(U_{\Et},R^q\nu_{U,*}F_G\bigr)=H^q(U_{\Proet},F_G)
=\operatorname{Ext}^q_{\Sh(S,A)}(G,A).
$$
By the choice of $G$ and $q$ in (iv) the right-hand side is nonzero for
arbitrarily large $q$, and $\Gamma$ is a functor to $A$-modules, so the
left-hand side is nonzero for those $q$; hence
$$
R^q\nu_{U,*}F_G\neq0\qquad\text{for arbitrarily large }q,
\qquad\text{that is,}\qquad
\operatorname{cd}_A(\nu_{U,*})=\infty .
$$
This is the failure proved in *The all-sheaves, uniform-in-the-base-change form of the comparison bound is false*: the
object $U$ of $X_{0,\Proet}$ is one of the pro-étale base changes over
which the bound $(\mathrm{G})$ is required, and $F_G$ is a sheaf of
$A$-modules on $U_{\Proet}$ with no constructibility hypothesis, so no
integer $M$ bounds the vanishing degree. Note that $S=\beta I\times\beta I$
is *not* extremally disconnected – the product of two infinite
extremally disconnected compact Hausdorff spaces never is – which is exactly
what allows the constant sheaf on $S$ to have infinite injective dimension
while the constant sheaf on each $U_T$ of (iii) is injective.
1. **(vii)** *What the counterexample does not affect.* On the
blueprint's coefficient class [def-sf-fullcd-used-class] – the sheaves of
étale origin, equivalently the constructible ones – the bound is $M=0$,
by [prop-sf-comparison-bound-zero], so the vanishing required by
[def-weil-full-cohomological-dimension] holds there with the bound
$2d$, which is [thm-sf-fullcd-used-class]; the counterexample uses a
sheaf $F_G$ that is not of étale origin. Two further consequences are
recorded here for the status of the neighbouring items. First, by
*The strictly henselian limit has no higher cohomology*(iii) the limit object
$\Spec\mathcal O^{\mathrm{sh}}_{U,\bar u}$ of a geometric point of $U$ has
no higher cohomology for any sheaf, and by the contrapositive of
*Continuity for arbitrary sheaves implies the vanishing* the present computation
shows that the continuity statement $(\mathrm{C}_q)$ of that theorem
*fails* at $U$, in those degrees $q$ in which
$R^q\nu_{U,*}F_G\neq0$; the continuity route is therefore not a residue
"for arbitrary sheaves" but a statement about the finite-type models, which is
the form in which *Continuity for arbitrary sheaves gives the full cohomological-dimension bound* consumes it. Second,
nothing here weakens any statement of this chapter: the class form
[thm-sf-fullcd-used-class] and the sharp comparison bound
[prop-sf-comparison-bound-zero] are unconditional on that class, and the
only statement that changes status is $(\mathrm{G})$ itself, which passes
from "open" to "false".
