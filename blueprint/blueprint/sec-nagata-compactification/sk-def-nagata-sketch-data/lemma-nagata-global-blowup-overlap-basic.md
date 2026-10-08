+++
id = "lemma-nagata-global-blowup-overlap-basic"
kind = "lemma"
title = "The basic-overlap comparison is an isomorphism"
order = 50
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isPullback_blowupNatTrans_of_basicOpen"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-restrict", "prop-nagata-rees-graded"]
+++
The constructed map $\omega_{ij,s}$ is an isomorphism over $D(s)$.

## Proof

Quasi-coherence identifies both restricted ideals with the same localized
ideal. Thus $r_{i,s}$ and $r_{j,s}$ are isomorphisms by
[prop-nagata-affine-blowup-restrict]; their composite with the inverse
of $r_{i,s}$ is an isomorphism, with inverse $r_{i,s}\circ r_{j,s}^{-1}$.
