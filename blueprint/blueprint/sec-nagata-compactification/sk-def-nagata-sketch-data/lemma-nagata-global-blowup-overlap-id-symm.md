+++
id = "lemma-nagata-global-blowup-overlap-id-symm"
kind = "lemma"
title = "Identity and symmetry of overlap isomorphisms"
order = 52
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.blowupNatTrans_equifibered"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-global-blowup-overlap-independent", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
The overlap isomorphism of a chart with itself is the identity, and the
overlap isomorphism from chart $i$ to chart $j$ is inverse to the one from
$j$ to $i$.

## Proof

On a basic refinement, $\omega_{ii,s}=r_{i,s}r_{i,s}^{-1}=1$ and
$\omega_{ji,s}\omega_{ij,s}=r_{j,s}r_{i,s}^{-1}r_{i,s}r_{j,s}^{-1}=1$.
The equalities descend from the basic cover.
