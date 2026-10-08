+++
id = "lem-pur-dnc-section-geometry"
kind = "lemma"
title = "Geometry of the deformation"
order = 1998
uses = ["cor-pur-vector-bundle-purity", "def-pur-co-smoothness", "def-pur-conventions", "def-pur-dnc-section-family", "def-pur-normal-bundle", "def-pur-section-invariant", "def-weil-scheme-morphism-properties", "lem-pur-regular-immersion-linearization", "sbc-thm-etale-local-normal-form"]
lean = ["AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), in the situation of
[def-pur-dnc-section-family] with $g:V\to B$ smooth of pure
relative dimension $d$ and $N_s\to B$ the normal bundle of the
section:

1. *the fibers.* The fiber of $\widetilde g$ over $1$ is
$(g:V\to B,s)$ and the fiber over $0$ is the
$\pi_N:N_s\to B$ with its zero section; hence by the
base-change compatibility of [def-pur-co-smoothness]
(applied to the closed immersions $i_1,i_0$ of the two
sections of $\mathbf A^1_B$),
$$
\qquad i_1^*F\simeq C(g,s),\qquad
i_0^*F\simeq C(\pi_N,0_N).\qquad\text{(the two fibers)}
$$
1. *the coordinates.* Since $s$ is a section of a smooth
map, etale-locally there are coordinates $x_1,\dots,x_d$ on
$V$ over $B$ in which $s$ is given by $x_i=0$ (the
relative form of the local linearization of
[lem-pur-regular-immersion-linearization], via
[sbc-thm-etale-local-normal-form]); on the DNC chart the
coordinates are $u_i=x_i/t$, so $\widetilde g$ is smooth of
pure relative dimension $d$.
1. *the punctured trivialization.* Over $\mathbf G_{m,B}$
the deformation space is canonically
$$
D_sV|_{\mathbf G_{m,B}}\simeq V\times_B\mathbf G_{m,B},
\qquad \widetilde s|_{\mathbf G_{m,B}}=s\times 1,
$$
so base change for the cohomologically smooth $\widetilde g$
gives the canonical isomorphism
$$
\kappa^\circ:j^*F\;\xrightarrow{\ \sim\ }\;j^*a^*C(g,s),
\qquad a:\mathbf A^1_B\to B.
$$
1. *the standard pair.* For the standard pair
$(\mathbf A^d_B\to B,0)$, the deformation space is
$\mathbf A^d_{B}\times_B\mathbf A^1_B$ with $x_k=tu_k$, the
family object is the pullback $a^*\bigl(0^*\omega_{\mathbf A^d_B/B}\bigr)$, and $0^*\omega_{\mathbf A^d_B/B}=\Lambda(d)[2d]$ by the vector-bundle purity of
[cor-pur-vector-bundle-purity].
1. *base change.* The Rees-algebra description of the
deformation space for a closed section, the punctured
trivialization, and the family object commute with base change
in $B$.

## Proof

Use the blow-up construction of [def-pur-dnc-section-family] and the section invariant of [def-pur-section-invariant]. The local coordinates are those of [sbc-thm-etale-local-normal-form], and the comparison of family fibers uses condition (3) of [def-pur-co-smoothness].
Item (1): the blow-up along $s(B)\times\{0\}$ is fiberwise trivial
away from the center, and the strict transform of
$V\times_B\{0\}$ is removed; the fiber of $\widetilde g$ over
$t\neq0$ is $V$ with the section $s$, and the exceptional
division of the affine cone identifies the fiber over $0$ with the
normal bundle $N_s$ of the section. Items (2): the coordinates are
the ones of the relative linearization; on the chart
$u_i=x_i/t$, the map $\widetilde g$ is the projection
$(u,x',t)\mapsto(x',t)$ into the base coordinates, smooth of
relative dimension $d$; on the remaining charts of the blow-up the
same computation after substituting a generator of the center gives
smoothness. Items (3),(4),(5) are the standard Rees-algebra
calculations, with the normal-bundle identification of
[def-pur-normal-bundle] and its base-change behavior; the family
object of the standard pair is computed by the rank-$d$ vector-bundle
purity of [cor-pur-vector-bundle-purity] since
$\mathbf A^d_B\to B$ is the trivial rank-$d$ bundle.
