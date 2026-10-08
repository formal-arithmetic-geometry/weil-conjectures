+++
id = "lemma-nagata-global-blowup-overlap-cocycle"
kind = "lemma"
title = "Triple-overlap cocycle"
order = 53
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.blowupNatTrans_equifibered"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-affine-blowup-restrict-cocycle", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-global-blowup-overlap-independent", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-rees-graded"]
+++
On every triple overlap, the composite of the $(i,j)$ and $(j,k)$ overlap
isomorphisms equals the $(i,k)$ overlap isomorphism.

## Proof

Cover the triple overlap by basic affine opens. On each such open,
$\omega_{jk,s}\omega_{ij,s}=r_{k,s}r_{j,s}^{-1}r_{j,s}r_{i,s}^{-1} =r_{k,s}r_{i,s}^{-1}=\omega_{ik,s}$; this is precisely the affine
restriction cocycle. Equality on the cover proves the claim.
