+++
id = "lemma-nagata-global-blowup-overlap-independent"
kind = "lemma"
title = "Independence of the basic refinement"
order = 51
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.blowupNatTrans_equifibered"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-affine-blowup-restrict-cocycle", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
On the intersection of two chosen basic refinements, the two overlap
constructed maps $\omega_{ij,s}$ agree.

## Proof

Refine once more to a basic open contained in both. There the two maps are
the same composite of restriction isomorphisms, by
[lemma-nagata-affine-blowup-restrict-cocycle]. Since these refinements
cover the source overlap, equality of morphisms follows by locality on the
source.
