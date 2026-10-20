# AlgebraicGeometry.Scheme.FiniteEtale.finiteEtale_fieldLimit_descent

## Reason

Implement the proof using private diagram, cone, and pullback comparison helpers.
The preflight classifies the three private instances and local irreducibility
attributes as command/interface changes and therefore requests this record.
The two original public constructions and the theorem signature are unchanged.
No target definition or statement changes meaning.

## Old

No private helper declarations or local transparency attributes. The theorem body
was `sorry`.

## New

Private instances `fieldBase_compact`, `fieldBase_qs`, and `fieldDiagram_affine`
provide qcqs field base changes and affine transition maps. They prove existing
geometric properties using Mathlib's base-change instances. The command
`attribute [local irreducible] coverIso pullbackAssocCover` keeps proof search from
unfolding large pullback comparison terms; explicit projection and naturality
lemmas provide their API. The limit helper uses Mathlib's
`isLimitOfIsPullbackOfIsConnected` with the canonical second projections and
`IsCofiltered.isConnected`; this avoids the large manual universal-property
construction. Two declaration-local
`set_option backward.isDefEq.respectTransparency false in` commands support the
limit proof and theorem elaboration. No public declaration signature changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent | T9 | Original hole closed; private helpers added. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.AlgebraicFieldLimit | unclaimed | Uses the unchanged theorem; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath | V9 | Direct importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport | unclaimed | Direct importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1 | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.WeilTwistedPaths | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.Paper.DenseOpenPiOneSurjective | E3 | Indirect importer; unchanged interface. |
| Sheaf.Paper.FiniteConstantH1Pi1 | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.Paper.RealBoundaryLocalConstants | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | Indirect importer; unchanged interface. |
| Sheaf.Paper.RealSheafSections | unclaimed | Indirect importer; unchanged interface. |

## Status

landed 20261020T131153-L-1252967 2026-10-20 (merge of deliver/T9/Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent)
