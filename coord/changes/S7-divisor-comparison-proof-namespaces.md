# divisorLineBundle_agrees_sc proof namespaces

## Reason

The completed proof uses monoidal isomorphisms, opens, opposite objects and the local generator
API. Its file-local open command now also opens MonoidalCategory, TopologicalSpace and Opposite.
The static delivery checker classifies any changed open command as an interface change.
No declaration signature, definition, public import, attribute, notation or instance changes.
All added helpers are private and fully proved. Proof imports remain private.

## Old

```lean
open CategoryTheory AlgebraicGeometry
```

## New

```lean
open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
```

## Users

Read-only `tools/downstream.py Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC --uses
 divisorLineBundle_agrees_sc` lists the following five downstream modules and the item itself
as a declaration-name hit. Claim records for the five consumers are absent (unclaimed).
The file-local open command does not propagate to importing modules, and the public theorem
signature stays verbatim. None requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC | S7 | Completed proof; same public statement |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Existing theorem use unchanged |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Transitive consumer; unchanged |
| Sheaf.AlgebraicGeometry.Curve.DegreeNormalizedTrace | unclaimed | Transitive consumer; unchanged |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Transitive consumer; unchanged |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | Transitive consumer; unchanged |

No target statement or definition meaning changes. No consumer file is edited.

## Status

landed 20261023T124409-L-1394204 2026-10-23 (merge of deliver/S7/Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC)
