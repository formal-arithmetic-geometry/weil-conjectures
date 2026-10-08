+++
id = "thm-pur-cohomological-smoothness"
kind = "theorem"
title = "Cohomological smoothness of smooth morphisms"
order = 1996
uses = ["def-coefficient-twists-detailed", "def-pur-co-smoothness", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-co-smooth-composition", "lem-pur-co-smooth-etale-locality", "lem-pur-smb-extraordinary", "prop-asd-smooth-base-change", "sbc-thm-etale-local-normal-form", "thm-asd-smooth-tensor", "thm-sf-ambient-adjoint-class", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
for every smooth separated morphism $f:X\to Y$ of relative dimension
$d$ put

$$
\omega_f\;=\;Rf^!\Lambda_Y.
$$

Then:

1. *Tensor formula.* For every $K\in D^b_{ctf}(Y,\Lambda)$ the
canonical map
$$
Lf^*K\otimes^L_{\Lambda_X}\omega_f\xrightarrow{\ \sim\ }Rf^!K
$$
is an isomorphism.
1. *Invertibility.* $\omega_f$ is invertible.
1. *Base change.* The formation of $\omega_f$ and of the
canonical map is compatible with arbitrary base change: for a
Cartesian square with $f'$ the base change of $f$,
$$
Lu^*\omega_f\xrightarrow{\ \sim\ }\omega_{f'},
$$
and the two canonical maps correspond under $Lu^*$; this holds for
*arbitrary* $v$ by [lem-pur-smb-extraordinary].
1. *Composition.* The tensor formula is compatible with
composition of smooth morphisms, through the composition isomorphism
for $R^!$ of [def-weil-exceptional-inverse-image].

(*Orientation-free form*: none of the four statements identifies
$\omega_f$ with a twist and a shift; that identification,
$\omega_f\cong\Lambda(d)[2d]$, is the content of
[thm-pur-diagonal-dualizing-object] proved below from the diagonal
argument.)

## Proof

Work at a finite coefficient stage. The earlier orientation-free
theorem [thm-asd-smooth-tensor] proves the canonical tensor
formula on the ordinary etale site and shows that
$\omega_f[-2d]$ is a locally constant free rank-one sheaf.
In particular it is tensor-invertible, and tensoring it with the
pullback of a bounded constructible finite-Tor complex stays in that
category. The actual-adjoint comparison
[thm-sf-ambient-adjoint-class] and
[thm-weil-pbc-site-comparison] transport the tensor map and
its isomorphy to the finite etale-origin objects used here.
Because the map is obtained by transposing the projection formula
and counit on both sites, the transported map is the canonical
$\theta_{f,K}$ in [def-pur-co-smoothness].

For the third condition of that definition,
[lem-pur-smb-extraordinary] proves arbitrary base change of the
actual right adjoint, and [prop-asd-smooth-base-change] also
proves its compatibility with the tensor transformation before
transport. Thus these are all three conditions of cohomological
smoothness. For composition, [lem-pur-co-smooth-composition]
identifies $\omega_{gf}$ with
$\omega_f\otimes^LLf^*\omega_g$. The two tensor transformations
agree: transposing them gives the projection formula followed by
the same two counits, composed in their adjunction order. This
proves the fourth assertion without using an orientation of $f$.
