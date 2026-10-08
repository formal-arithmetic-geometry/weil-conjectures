+++
id = "lem-weil-pbc-etale-finite-data-descent"
kind = "lemma"
title = "Finite-presentation data at an inverse limit"
order = 950
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions"]
+++
Let $X=\varprojlim_iX_i$, where the $X_i$ are quasi-compact and
quasi-separated [def-weil-pbc-scheme-conventions] and the transition maps are
affine. Quasi-compact quasi-separated etale $X$-schemes of finite
presentation, finite diagrams of these schemes, and equalities of their
morphisms descend to some $X_i$. A finite family that is a covering
[def-weil-pbc-etale-site] at the limit is a covering at every sufficiently
late stage of a descended diagram.

## Proof

First suppose the schemes are affine. An algebra of finite presentation is
specified by finitely many generators and relations. Every coefficient in
these expressions occurs at one common stage of the filtered colimit of
coordinate rings. A morphism is specified by finitely many images of
generators; its relations and an equality of two such morphisms hold at a
later common stage. Etaleness descends by a finite standard-etale affine
presentation: the equations, the inverse of the relevant Jacobian
determinant, and the finitely many identities asserting that the chosen opens
cover are all finite algebraic data. These are elementary finite-presentation
and localization calculations.

In the quasi-compact quasi-separated case of
[def-weil-pbc-scheme-conventions], choose finitely many affine opens at a
fixed base stage and pull them back. Choose finitely many affine presentation
charts of the object above them. Their overlaps have finite affine covers, by
quasi-separatedness. Descend the gluing maps and their inverses on these
covers by the affine calculation. The cocycle identities on triple overlaps
hold at a common later stage, again by a finite affine cover and the equality
calculation. Gluing gives the required descended scheme and morphisms. This
proves the finite-diagram assertion.

For the covering assertion, the images of finitely many quasi-compact etale
maps form a quasi-compact open, and their union commutes with base change: a
nonempty fibre remains nonempty after extension of its residue field. The
complement is constructible. If its pullback to every later stage were
nonempty, these constructible complements, with their constructible
topologies, would form a system of nonempty compact Hausdorff spaces. An
inverse system of such spaces has nonempty limit: the finitely many
compatibility conditions on a finite product can always be met at a common
later stage, so compactness applies. A compatible family of scheme points
gives a point of the inverse-limit scheme for affine transition maps, as
follows locally by taking the union of the compatible prime ideals in the
colimit ring. This would give a point outside the covering at the limit, a
contradiction. Thus the complement is empty at some stage. This is precisely
surjectivity of the family in [def-weil-pbc-etale-site]. For comparison with
the usual finite-presentation formulation, see
[Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM); the
finite data and the covering argument have been specified above.
