+++
id = "lemma-weil-pbc-derived-exchange-coherence"
kind = "lemma"
title = "Resolution independence, identities, and pasting"
order = 1046
lean = ["AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_ext", "AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz", "AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert"]
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "def-weil-pbc-underived-exchange", "lemma-weil-pbc-derived-exchange-replacement"]
+++
The class $\operatorname{Ex}_{\square,K}$ is independent of the injective
resolution and is compatible with identity squares, horizontal pasting, and
vertical pasting.

## Proof

Given two injective resolutions, the comparison theorem supplies chain maps
each way, unique up to chain homotopy, whose composites are homotopic to the
identities. Naturality of the degreewise exchange map sends these homotopies
to homotopies after both direct images; localization therefore gives the same
derived morphism. For the identity square, the unit followed by the counit is
the identity sectionwise, hence degreewise. For pasted squares, expand each
exchange as ``unit, pullback identification, counit''; the two middle
identifications are equal by associativity of fibre products, and the two
adjunction triangle identities cancel the adjacent unit–counit pairs. The
same calculation with the order reversed proves vertical pasting.
