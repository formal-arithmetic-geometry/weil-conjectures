+++
id = "thm-sc-jacobian-representability"
kind = "theorem"
title = "The Jacobian over a separably closed field"
order = 850
uses = ["def-pc-genus", "def-pc-geometrically-irreducible", "def-pc-smooth-projective-curve", "def-sc-abelian-variety", "def-sc-jacobian", "def-sc-pic0", "def-sc-picard-functor", "lem-pc-curves-are-sc", "lem-pc-picard-functor-agrees-sc", "lem-sc-abelian-variety-projective", "lem-sc-pic-tangent-space", "prop-pd-picard-degree-decomposition", "thm-pc-picard-representable", "thm-sc-theorem-of-the-base"]
lean = ["AlgebraicGeometry.exists_jacobian"]
+++
Let $k$ be a separably closed field and let $C$ be a
smooth projective curve over $k$
which is geometrically integral,
of genus $g=g(C)=\dim_kH^1(C,\mathcal O_C)$ ([def-pc-genus]). There is
an abelian variety $J_C$ over
$k$, the *Jacobian* of $C$ in the sense of [def-sc-jacobian], of dimension $g$, together
with a natural isomorphism of group-valued functors

$$
\operatorname{Pic}^0_{C/k}\cong h_{J_C},
$$

where $\operatorname{Pic}^0_{C/k}$ is the degree-zero part of the
Picard functor; its $k$-points are the
invertible modules of degree $0$ on $C$, and for algebraically closed
$k$ they are the $\operatorname{Pic}^0(C)$ of [def-sc-pic0], so that
$\operatorname{Pic}^0(C)=J_C(k)$ canonically in that case. Moreover $J_C$
is compatible with base change along extensions of separably closed fields:
$J_{C_{k'}}\cong(J_C)_{k'}$ for $k\subseteq k'$ separably closed.
The scope of this result, and the case of a general ground field, are
discussed in a remark below in this chapter.

## Proof

[thm-pc-picard-representable] of the Picard chapter – the Picard functor
of a smooth projective curve over a separably closed field is
representable, with the full decomposition carried out there (*reference: Stacks Project, Picard Schemes of Curves, Proposition 44.6.6, [Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)*); cf. Mumford, Abelian Varieties; Milne, Abelian Varieties, Ch. 12. We outline the
classical construction; the existence and property statements are
theorems of the sources above.

*(1) The Picard functor.* $\operatorname{Pic}_{C/k}$ and
$\operatorname{Pic}^0_{C/k}\subseteq\operatorname{Pic}_{C/k}$ are
as in [def-sc-picard-functor]; for $k$ algebraically closed, $C$ is a
smooth connected curve in the sense of [def-sc-pic0] by
[lem-pc-curves-are-sc], and
$\operatorname{Pic}^0_{C/k}(k)=\operatorname{Pic}^0(C)$ of
[def-sc-pic0].

*(2) Representability.* The theorem of Grothendieck states
that $\operatorname{Pic}_{C/k}$ (which is the functor of [def-pc-picard-functor] by [lem-pc-picard-functor-agrees-sc]) is represented by a group scheme
locally of finite type over $k$ ([thm-pc-picard-representable] of the Picard chapter; *reference: Stacks Project, Picard Schemes of Curves, Proposition 44.6.6, [Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)*). The
subfunctor $\operatorname{Pic}^0_{C/k}$ is represented by an open
and closed subgroup scheme ([prop-pd-picard-degree-decomposition],
parts (2) and (3)).

*(3) Smoothness and the tangent space.* By
[lem-sc-pic-tangent-space], the tangent space of
$\operatorname{Pic}_{C/k}$ at the identity is
$H^1(C,\mathcal O_C)$, of dimension $g$ ([def-pc-genus]);
by [thm-sc-theorem-of-the-base],
$\operatorname{Pic}_{C/k}$ is a disjoint union of smooth
varieties of dimension $g$.

*(4) Properness.* $\operatorname{Pic}^0_{C/k}$ is proper by
[thm-sc-theorem-of-the-base] (the ``theorem of the base'').

*(5) Abelian variety and base change.* By (2)–(4),
$J_C:=\operatorname{Pic}^0_{C/k}$ is a proper smooth connected
group scheme, i.e. an abelian variety
([def-sc-abelian-variety]), of dimension $g$. For
$k$ algebraically closed, $J_C(k)=\operatorname{Pic}^0(C)$
([def-sc-picard-functor], [def-sc-pic0]) by
representability, and base change
compatibility $J_{C_{k'}}\cong(J_C)_{k'}$ holds because the Picard
functor commutes with base change. Finally, $J_C$ is projective
by [lem-sc-abelian-variety-projective].

The hypothesis that $k$ is separably closed enters this proof exactly as in
the Picard chapter: it is what produces a $k$-rational point of $C$, from
which the representability theorem [thm-pc-picard-representable] of that
chapter deduces the fppf sheaf property of the naive Picard presheaf and hence
representability. For a curve over a general ground field the conclusion is
not asserted in this blueprint; see [rem-sc-jacobian-scope].
