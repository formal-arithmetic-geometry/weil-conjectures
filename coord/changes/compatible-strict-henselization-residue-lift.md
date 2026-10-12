# exists_compatibleStrictHenselizationResidueLift

## Reason
The proof-only imports are changed to include the intermediate ind-etale chart theorem and remove direct implementation imports.

## Old
The module imported `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples` and `Sheaf.RingTheory.StrictHenselizationTriples` directly.

## New
The module imports `Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale` and uses its public theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | G3 | imports the target; unchanged signature |

## Status
landed 20261012T173839-L-3299386 2026-10-12 (merge of deliver/K2/Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift)
