# exists_derivedProjectionMate_openRestriction_comparison proof scope

## Reason

The static delivery checker classifies file-level option and attribute commands as
interface changes. These commands are local elaboration controls. They prevent
unfolding of fixed derived constructions in the proof, resolving the previous
60-second compiler timeout. They do not change any declaration's signature,
visibility, definition or downstream statement. The three new public theorems
have new DAG nodes and are used only by proof imports of the item.

## Old

```lean
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry
```

## New

```lean
universe u w
open CategoryTheory MonoidalCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry

attribute [local irreducible] derivedPullback schemeDerivedTensorMonoidal
  HasDerivedCategory.ofIsGrothendieckAbelian Functor.mapDerivedCategory
  DerivedCategory.homologyFunctor
```

The item's theorem also has a declaration-local maxHeartbeats setting of 800000.
The single-file compiler's 60-second wall-clock limit is unchanged.

## Users

`tools/downstream.py --uses exists_derivedProjectionMate_openRestriction_comparison`
reports two textual users. No consumer needs adaptation: the original signature,
public imports and definitions are unchanged; the attributes have local scope.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison | F2 | proof elaboration only |
| Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses | unclaimed | unchanged signature and meaning |

## Status

landed 20261013T142855-L-497118 2026-10-13 (merge of deliver/F2/Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison)
