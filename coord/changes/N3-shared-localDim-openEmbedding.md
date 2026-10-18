# AlgebraicGeometry.localDim_openEmbedding

## Reason

Return 5d2bdf5da correctly identified that the item's private open-embedding lemma
already exists verbatim in
`Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension`.
The existing lemma is private, so importing its module alone cannot reuse it.
Expose that existing proved lemma in place, add its docstring, remove the duplicate
from the item, and add a private proof import of the existing module. The existing
module was unclaimed when this repair began. No proof or mathematical statement
of that module changes; no target definition or signature changes.

## Old

In `Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension`:

```lean
private theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x)
```

The item independently proved the same private statement.

## New

In the same existing module, with the same proof:

```lean
theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x)
```

The item removes its copy and uses the now-public existing lemma through:

```lean
import Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
--uses AlgebraicGeometry.localDim_openEmbedding` lists the two existing transitive
importers below and finds only the defining module's existing local use of this name.
Neither importer changes. The new private import in the item exposes no new
statement dependency to its own importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension | unclaimed | Existing helper becomes public; its type and proof stay identical. |
| Sheaf.AlgebraicGeometry.RationalPointLocalDimensionBaseChange | unclaimed | Unchanged; compiled against the exposed helper. |
| Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension | unclaimed | Unchanged; compiled against the exposed helper. |
| Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange | N3 | Duplicate removed; proof uses the existing helper. |

## Status

landed 20261018T071206-L-1672852 2026-10-18 (merge of deliver/N3/Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange)
