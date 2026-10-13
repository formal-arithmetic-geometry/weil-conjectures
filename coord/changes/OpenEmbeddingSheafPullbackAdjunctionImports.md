# OpenEmbeddingSheafPullbackAdjunction import cleanup

## Reason
The original public import of Mathlib.CategoryTheory.Preadditive.Injective.Preserves is unused by the item's statement and proof. Remove it, and import the new monomorphism lemma privately because only the proof uses it. This record concerns imports only: no existing statement, definition, visibility, or elaborated type changes, and no target-definition review is reopened.

## Old
```lean
module
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
```

## New
```lean
module
public import Mathlib.Topology.Sheaves.Abelian
import Sheaf.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackMonomorphisms
```

## Users
The downstream --uses check found just the item and its direct importer as textual users of isOpenEmbedding_sheafPullback_adjunction. There are 826 transitive downstream modules, but the only direct importer imports this item privately and itself publicly imports Mathlib.CategoryTheory.Preadditive.Injective.Preserves, so all transitive import availability is preserved. No module needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackAdjunction | D3 | Same theorem signature and definitions; remove unused public import and add proof-only dependency. |
| Sheaf.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackInjectives | unclaimed in local claims | No change: already publicly imports both original Mathlib imports; theorem application and statement unchanged. |

## Status
landed 20261013T010612-L-2669946 2026-10-13 (merge of deliver/D3/Sheaf.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackAdjunction)
