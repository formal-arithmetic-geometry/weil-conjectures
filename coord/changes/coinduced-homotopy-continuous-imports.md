# Rep.exists_coinduced_continuous_contraction: public import pruning

## Reason

The contraction is constructed directly from locally constant functions and compactness.
Neither the coinduced embedding theorem nor the abelian-category theorem is used.
Replace their imports with the foundational definitions needed by the unchanged statement.
The only interface change is the removal of these incidental public reexports.
No definition, theorem signature, or target meaning changes.

## Old

```lean
public import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.CategoryTheory.DiscreteModulesAbelian
```

## New

```lean
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Compactness.Compact
```

## Users

The complete transitive consumer set was obtained with tools/downstream.py.
All five unchanged sources were compiled in import order against the modified module
with lcompile.py --all; all passed. They are not included in the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | Original source compiles against the pruned imports; no edit. |
| Sheaf.RepresentationTheory.CoinducedContinuousAcyclic | K4 | Original source compiles against the pruned imports; no edit. |
| Sheaf.RepresentationTheory.CoinducedHomotopyIdentity | P1 | Original source compiles against the pruned imports; no edit. |
| Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants | unclaimed | Original source compiles against the pruned imports; no edit. |
| Sheaf.RepresentationTheory.DiscreteContinuousCohomology | unclaimed | Original source compiles against the pruned imports; no edit. |

The two direct consumers already import CoinducedDiscreteEmbedding independently.
ContinuousCochainsDerivedInvariants independently imports both removed modules.
DiscreteContinuousCohomology and FieldDiscreteModules retain their needed interfaces
through their own public imports. There are no forced adaptations.

## Status

landed 20261018T062840-L-667092 2026-10-18 (merge of deliver/N4/Sheaf.RepresentationTheory.CoinducedHomotopyContinuous)
