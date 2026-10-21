# AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_coefficient_naturality

## Reason

Restore the assigned quarantined module identified by coord/rework.tsv. Its archive
publicly imports the withdrawn, empty Sheaf scalar operations module. The scalar
operations used by the theorem now belong to the canonical upstream module.
The original theorem and its complete proof must be retained.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The theorem signature, visibility, docstring and proof are unchanged from the
quarantine archive. Both proof-only imports are retained. No definition or target
statement changes. The node already attaches its scalar operations dependency to
the canonical upstream module, and its proof steps still match the proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | S1 | Restored with the canonical public scalar operations import. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | quarantined | Sole archived direct importer and theorem user; same theorem and operations. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | quarantined | Transitive consumer; same statements and operations. |

Searched both lean/ and quarantine/ for module imports and theorem uses.
There are no live Lean importers. tools/downstream.py reports unknown module(s)
because the item is quarantined; the archived consumer was therefore inspected
explicitly. Its own public import still names the empty scalar operations module,
which requires a separate restoration repair. This import repair causes no new
consumer error and changes no mathematical interface. No consumer adaptation is
forced. The unit route and all DAG dependencies remain intact.

## Status

landed 20261021T001141-L-1377660 2026-10-21 (merge of deliver/S1/Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality)

Compilation and consumer checks remain pending: the published server build lacks
ScalarCupPullbackNaturality.olean. Both delivery attempts pushed nothing.
