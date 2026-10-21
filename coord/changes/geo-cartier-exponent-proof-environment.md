# SheafOfModules.GeoCartierExponent.geoCartier_exponent_independence

## Reason

The proof needs the `CategoryTheory.Pretriangulated` namespace for the exact Hom sequence,
scalar-first tensor notation from `ChangeOfRings`, and the standard local instances for
composition of finite-limit/finite-colimit preserving functors. The latter instances are
used to apply the existing derived-composition shift compatibility results. The additional
linter setting suppresses unused section-instance warnings in private helpers.

Preflight conservatively classifies these file commands as an interface change and requires
this record. They configure proof elaboration in this file; they change no declaration
signature, existing definition body, public import, target statement, or exported instance.
The seven existing declarations before the target are verbatim unchanged. No consumer needs
adaptation, and no target's meaning changes.

## Old

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wZ wM wN
open CategoryTheory CategoryTheory.Limits
```

## New

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v r wZ wM wN
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ChangeOfRings
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

## Users

`tools/downstream.py Sheaf.Paper.GeoCartierExponentIndependence --uses
geoCartier_exponent_independence` lists the item itself as the only textual user of the
specified theorem and the following 17 downstream modules. The direct Lean importer is
GeoCartierCycleClass. All public signatures and existing definition bodies are unchanged.
The table includes the whole downstream set for the independent reader; none is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeoCartierExponentIndependence | G2 | New private proof helpers and proof environment; target hole closed |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | unclaimed | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | unclaimed | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C3 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | P4 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | G4 | No interface change or adaptation |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | No interface change or adaptation |
| Sheaf.Paper.PurityFrameClass | unclaimed | No interface change or adaptation |
| Sheaf.Paper.PurityFrameKummer | unclaimed | No interface change or adaptation |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | No interface change or adaptation |

## Status

landed 20261021T002140-L-1491892 2026-10-21 (merge of deliver/G2/Sheaf.Paper.GeoCartierExponentIndependence)
