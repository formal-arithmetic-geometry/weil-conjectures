# AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars

## Reason

The new section variables bind private, proved helpers for exact localization of
natural transformations and evaluation. No existing interface or definition changes.

## Old

The module had no `ExactTransformations` private-helper section. All existing
public signatures, attributes, imports, instances and non-theorem bodies are retained.

## New

A private-helper section proves the representative, whiskering, uniqueness and
evaluation equations for exact localization of natural transformations. Only
`evaluation_alpha` has its original `sorry` replaced by a proof. No helper appears
in a public signature or definition; the other three original holes are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars | F3 | Private proof helpers and evaluation_alpha proof only. |

No public interface or definition changes; no consumer adaptations are required.

## Status

landed 20261025T201851-L-2631992 2026-10-25 (merge of deliver/F3/Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars)
