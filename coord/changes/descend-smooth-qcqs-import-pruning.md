# DescendSmoothQcqs public import pruning

## Reason

The theorem assumes a limiting cone, so it does not use the separate construction of an
affine-transition limit. Its proof instead uses the existing base-change limit API in
WeilConjectures and the proved affine-diagram smoothness descent theorem. Remove the unused
public import of LimitAffineTransition. All existing declaration signatures and meanings stay
identical; no public data definition is changed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

This import is removed. The public imports of Mathlib smoothness, quasi-separatedness and
Over.pullback remain; proof imports use AffineDiagramSmoothStage and the source library's
AffineTransitionLimit module. The exported theorem has its original signature verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DescendSmoothQcqs | E4 | proof completed; unused import removed |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | H5 | no signature or proof change |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | U2 | no signature or proof change |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | M3 | no signature or proof change |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | C6 | no signature or proof change |
| Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram | Q5 | imports LimitAffineTransition directly |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | D9 | no signature or proof change |

The complete downstream list was obtained with tools/downstream.py. No downstream file
mentions any of the three declarations of LimitAffineTransition; the direct consumer also
imports that module itself. No consumer adaptation is needed. Target statements and their
definitions are unchanged.

## Status

landed 20261018T062734-L-643547 2026-10-18 (merge of deliver/E4/Sheaf.AlgebraicGeometry.DescendSmoothQcqs)
