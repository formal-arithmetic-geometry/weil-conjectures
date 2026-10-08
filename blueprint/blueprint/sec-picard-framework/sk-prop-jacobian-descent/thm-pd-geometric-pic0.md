+++
id = "thm-pd-geometric-pic0"
kind = "theorem"
title = "The degree-zero Picard functor over a separable closure"
order = 858
uses = ["def-pc-genus", "def-pc-geometrically-irreducible", "def-pc-smooth-projective-curve", "def-pd-degree-morphism", "def-pd-separable-closure", "def-sc-abelian-variety", "def-sc-jacobian", "def-sc-pic0", "lem-pd-geometric-curve", "thm-sc-jacobian-representability", "thm-sc-theorem-of-the-base"]
+++
Let $k$ be a field, let $C$ be a
smooth projective curve over $k$
which is geometrically integral,
of genus $g$ ([def-pc-genus]), and let $k_s$ be a
separable closure of $k$. Then the
degree-zero part
$\operatorname{Pic}^0_{C_{k_s}/k_s}$ is representable, and the representing
object $J_s$ is an abelian variety over
$k_s$ of dimension $g$; moreover $J_s(k_s)=\operatorname{Pic}^0(C_{k_s})$
under the canonical identification of [def-sc-pic0].

## Proof

By [lem-pd-geometric-curve] the curve $C_{k_s}$ is a smooth projective
curve over the separably closed field $k_s$ of [def-pd-separable-closure]
which is geometrically integral of genus $g$
([def-pc-genus]). [thm-sc-jacobian-representability] therefore
produces an abelian variety $J_s$ over $k_s$ of dimension $g$, whose defining
property is the isomorphism $\operatorname{Pic}^0_{C_{k_s}/k_s}\cong h_{J_s}$
of [def-sc-jacobian], and it identifies $J_s(k_s)$ with the group
$\operatorname{Pic}^0(C_{k_s})$ of [def-sc-pic0]. That theorem
formulates its functor as the degree-zero part of the Picard functor, which is
the subfunctor introduced in [def-pd-degree-morphism]; hence $J_s$
represents $\operatorname{Pic}^0_{C_{k_s}/k_s}$ in the sense used here.
[thm-sc-theorem-of-the-base] supplies the same conclusion independently,
together with smoothness, properness and the dimension, which is what makes
$J_s$ an abelian variety in the sense of [def-sc-abelian-variety].
