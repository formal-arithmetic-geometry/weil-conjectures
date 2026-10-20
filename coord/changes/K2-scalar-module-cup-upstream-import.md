# scalarCup_moduleCup_compatibility

## Reason

Restore the assigned quarantined module after the 2026-10-20 upstream sync.
Its archived public scalar-cohomology provider is now an empty withdrawn module.
The actual scalarCohomology and scalarCohomologyCup declarations are available only
through private proof imports, so Lean rejects their use in the public statement.
Use the adopted upstream provider already recorded by
def-sc-field-linear-module-cohomology-operations.

## Old

In Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility:

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The module is absent from lean/ and preserved at the quarantine path recorded in
coord/rework.tsv. Its declarations and dependencies remain attached to their nodes.

## New

Restore the entire archived module with this single import replacement:

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

Every declaration, signature, attribute, docstring, and proof body is unchanged.
The three remaining imports are unchanged. No definition, statement, target, DAG
route, or source-library file changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility | K2 | Restored with its actual public provider; zero local holes. |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | unclaimed; quarantined | Existing direct caller and its signed theorem application remain valid; its own retired provider import needs separate rework. |

tools/downstream.py --allow-missing --uses scalarCup_moduleCup_compatibility
reports zero live users. Searching lean/ and quarantine/ finds the direct caller
above, whose node still cites lem-sc-scalar-cup-module-cup-compatibility.
No caller needs adaptation to a changed declaration: no declaration changed.
A scratch consumer publicly imports only the restored module, restates the exact
public theorem signature, and proves it by the existing theorem. It compiles with
the restored module through lcompile.py. The original archive fails with the
recorded unknown-public-identifier diagnostics, and the repaired module compiles.

## Status

landed 20261020T153009-L-2861923 2026-10-20 (merge of deliver/K2/Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility)
