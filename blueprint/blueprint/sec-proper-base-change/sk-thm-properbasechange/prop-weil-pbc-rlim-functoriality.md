+++
id = "prop-weil-pbc-rlim-functoriality"
kind = "theorem"
title = "Functoriality of the sequential derived inverse limit"
order = 1242
uses = ["def-weil-derived-limit", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-kinjective-resolutions", "prop-weil-pbc-derived-inverse-limit-computation"]
tags = ["latex:proposition"]
+++
Let $\operatorname{Tow}_{A}(T)$ be the tower category of
[def-weil-pbc-adic-coefficient-datum], an abelian category with enough
injectives. Fixing a functorial K-injective resolution
[def-weil-pbc-kinjective-resolutions] $M_\bullet\to I_\bullet$ of every
object of $\operatorname{Tow}_{A}(T)$, the assignment

$$
 \Rlim:D(\operatorname{Tow}_{A}(T))\longrightarrow D(T_{\Proet},A),
 \qquad
 M_\bullet\longmapsto\varprojlim_nI_n
$$

is a triangulated functor, and any two such choices of functorial K-injective
resolutions give isomorphic functors.

(*Source note:* functoriality of the derived limit is contained in Stacks
Project, Derived Categories, Definition 13.34.1 (Tag
[08TC](https://stacks.math.columbia.edu/tag/08TC)), whose triangle is natural
in the system, and the functorial K-injective resolutions fixed here are
those of Theorem 19.12.6 (Tag
[079P](https://stacks.math.columbia.edu/tag/079P)) together with the
existence statement of Lemma 13.34.3 (Tag
[0BK7](https://stacks.math.columbia.edu/tag/0BK7)). What Stacks does not
state, and what the blueprint adds, is the resulting assignment
$D(\operatorname{Tow}_A(T))\to D(T_{\Proet},A)$ as a triangulated functor,
together with the comparison of any two choices of functorial resolutions.)

## Proof

In a Grothendieck abelian category every complex admits a functorial
K-injective resolution, and quasi-isomorphic K-injective complexes are
chain-homotopy equivalent (Stacks Project, Theorem 19.12.6, Tag
[079P](https://stacks.math.columbia.edu/tag/079P)); applied to the tower
category of [def-weil-pbc-adic-coefficient-datum] this supplies the
functorial resolutions fixed in the statement. By
[prop-weil-pbc-derived-inverse-limit-computation] the value of the assignment
at $M_\bullet$ represents the derived limit $\Rlim M_\bullet$ of
[def-weil-pbc-derived-inverse-limit], and the derived limit is a triangulated
functor of the system, being the first term of the Roos triangle, which is
natural in the system; the assignment therefore inherits exactness on
distinguished triangles. A second choice of functorial K-injective
resolutions is related to the first by a chain-homotopy equivalence over each
object, and $\varprojlim_n(-)$ of a levelwise homotopy equivalence of towers
is a homotopy equivalence, so the two assignments agree up to a natural
isomorphism of functors. The K-injectivity used here is that of
[def-weil-pbc-kinjective-resolutions].
