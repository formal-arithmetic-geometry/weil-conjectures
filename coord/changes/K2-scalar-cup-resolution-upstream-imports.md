# scalarCup_resolution_class_compatibility

## Reason

Restore the quarantined root after the 2026-10-20 upstream sync. Its archive
imports both scalar-cohomology providers through direct and proof imports,
causing the recorded duplicate externalCupCoefficients declaration. Select the
upstream provider consistently in the root and its required positive-degree
dependency, and use the upstream tensor-unit proof.

The scalar providers' public declarations and definition bodies agree. Their
differences are copyright text and local-instance names. No declaration or
mathematical definition is changed, and the existing Koszul factor is retained.

## Old

In Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility:

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient
```

In Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility:

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

Every declaration signature, attribute, docstring, definition and proof body is
retained verbatim from the quarantine archive or current live dependency.

## New

In Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility:

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ScalarTensorUnitCoefficient
```

In Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility:

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

Only these three import lines change. No source-library file is edited, and no
node route or target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility | K2 | Root restored; two provider imports migrated; zero local holes. |
| Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility | unclaimed | Required dependency; one provider import migrated; existing hole retained. |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | unclaimed; quarantined | Direct caller; no changed declaration to adapt. Its provider migration is a separate downstream rework under the current cluster instruction. |

The source-only downstream tool cannot see the quarantined root. Searching both
live and quarantine sources finds the direct edges: root imports positive
comparison, and scalar/module comparison imports root. The external-cup comparison
imports the scalar/module comparison. Every higher parent and attachment remains
intact; none is withdrawn. The earlier caller migration is preserved in scratchpad
but not delivered. The maintainer retries the remaining cluster after this root
lands, as the current brief specifies.

## Status

landed 20261020T150652-L-2563862 2026-10-20 (merge of deliver/K2/Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility)
