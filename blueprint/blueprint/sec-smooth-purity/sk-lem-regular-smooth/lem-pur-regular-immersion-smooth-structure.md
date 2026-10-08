+++
id = "lem-pur-regular-immersion-smooth-structure"
kind = "lemma"
title = "A regular immersion of smooth schemes over a perfect field"
order = 2032
uses = ["def-pur-conventions", "def-pur-regular-immersion", "def-sbc-smooth-morphisms", "def-weil-scheme-morphism-properties", "lem-sc-smooth-regular"]
lean = ["AlgebraicGeometry.IsRegularImmersion.smooth_comp", "AlgebraicGeometry.IsRegularImmersion.ringKrullDim_stalk_add"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $i:Z\hookrightarrow X$ be a
regular closed immersion of pure
codimension $c$, with $X$ smooth over the perfect field $k$ and
$Z$ regular. Then both structure morphisms

$$
a_X:X\longrightarrow\operatorname{Spec}k,\qquad
a_Z:Z\longrightarrow\operatorname{Spec}k
$$

are smooth, and $a_Z=a_X\circ i$.
On a connected component of $X$ of dimension $n$, its nonempty
inverse image in $Z$ has pure dimension $m=n-c$.

## Proof

The codimension is the local dimension difference of [def-pur-regular-immersion], and smoothness has the meaning of [def-sbc-smooth-morphisms].
$X$ is smooth over the perfect field $k$ by hypothesis. A regular
finite-type $k$-scheme is smooth over the perfect field $k$
(*reference: Stacks Project, Commutative Algebra, Lemma
10.140.5, [Tag
00TV](https://stacks.math.columbia.edu/tag/00TV)*: a regular local $k$-algebra essentially of finite type with
residue field separable over $k$ is smooth; this is the standard
regular–smooth criterion over a perfect field, as recorded in
[lem-sc-smooth-regular] and the regular–smooth remarks of
Blueprints 06c and 52), so $a_Z$ is smooth. Smooth schemes over a field are regular,
and their connected components have a fixed dimension. On a component
of $X$ of dimension $n$, the pure-codimension condition gives
dimension $n-c$ for each component of $Z$ lying in it. The
identity $a_Z=a_X\circ i$ is the definition of $i$ as a morphism
over $k$.
