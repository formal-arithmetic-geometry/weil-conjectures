# Sheaf.Topology.TopologicalCocycleNaturality public import cleanup

## Reason

The proved naturality module does not use `Mathlib.CategoryTheory.Abelian.RightDerived`.
Its declarations use the public sheaf-cohomology and injective-Ext imports. Remove
this redundant public import as required by the stage-3 pruning rule. No declaration
signature, visibility, universe, hypothesis, or definition changes.

The only direct importer, `Sheaf.Topology.TopologicalInducedCocycleFormula`, already
publicly imports `Mathlib.CategoryTheory.Abelian.RightDerived` itself. Therefore the
removal cannot remove that API from this importer's scope or from what it re-exports.
No adaptation of the importer is required. No target statement or target-used
definition changes, so target statement review is not reopened.

## Old

```lean
public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
```

## New

```lean
public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import all Sheaf.Topology.TopologicalResolutionCocycleLift
```

The new import is proof-only. Its `all` modifier exposes the existing private
`sectionEquiv` and `sectionEquiv_apply` for reuse without duplicate declarations. All existing signatures and public visibility remain
identical. The scoped unused-variable linter option preserves the original names
of unused proposition binders inside the cocycle-formula hypothesis.

## Users

`tools/downstream.py Sheaf.Topology.TopologicalCocycleNaturality --uses
 topological_cocycle_naturality` finds the item itself and the following sole user.
The transitive downstream graph is unchanged, and the direct user's own public
RightDerived import protects every transitive user of that API.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Topology.TopologicalCocycleNaturality | G3 | Proves existing statement; removes redundant public import. |
| Sheaf.Topology.TopologicalInducedCocycleFormula | unclaimed | No edit needed: its independent public RightDerived import retains the API. |

The unchanged direct importer is compiled against the delivered module in the
sandbox for validation only; it is not part of the delivery.

## Status

landed 20261012T194115-L-456489 2026-10-12 (merge of deliver/G3/Sheaf.Topology.TopologicalCocycleNaturality)
