# AlgebraicGeometry.Etale.geometricStalk_projectiveLine_of_strictLocal

## Reason
The previous proof imported `GeometricStalk`, which imports this module and creates a cycle. The repaired proof imports the strict-local model module and composes its explicit equivalences.

## Old
The theorem was proved by applying `Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`.

## New
The theorem is proved from `Etale.projectiveLine_strictLocal_modelComparison` and the premise `hLocal`.

## Users

| module | group holding it | effect |
|---|---|---|
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | project | Its import of this module remains acyclic because this module no longer imports it. |

## Status
landed 20261012T002323-L-552422 2026-10-12 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction)
