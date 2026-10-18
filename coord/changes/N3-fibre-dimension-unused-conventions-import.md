# AlgebraicGeometry.fibre_dimension_after_base_change

## Reason

The proof uses Mathlib's `isPullback_fiberToSpecResidueField_of_isPullback` and
`pullbackSpecIso` directly. Neither the theorem's signature nor its proof needs the
base-change conventions re-export, which also imports module pullback and Picard theory.
Remove this unused public import. No declaration, definition, instance, signature or
existing docstring changes. No target meaning changes and no target review is reopened.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
```

The added proof import reuses the existing open-embedding lemma; its exposure in
place is recorded in `N3-shared-localDim-openEmbedding.md`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange --uses
AlgebraicGeometry.fibre_dimension_after_base_change` currently lists two transitive
importers. `ProperTorsionDirectImageBound` is the only direct importer and actual
user of the theorem. It imports this item privately and does not need the removed
public re-export: its unchanged source compiles against the edited item.
`ProperDerivedDirectImageCoproducts` imports that consumer privately and sees the
same public interface. No consumer statement changes or adaptations are needed.
This replaces the retained delivery's outdated consumer list.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Unchanged; compiled against edited item. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Unchanged public interfaces through its direct dependency. |

## Status

landed 20261018T071206-L-1672852 2026-10-18 (merge of deliver/N3/Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange)
