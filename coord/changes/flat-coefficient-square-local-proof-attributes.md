# FlatCoefficientSquareNormalization local proof attributes

## Reason

The completed combining proof checks several large derived and section comparison
squares. Local irreducibility prevents geometric pullback, sheafification and derived
comparison constructions from expanding during these checks. The main proof compiled
in 32.7 seconds after this change. These local commands preserve all public signatures,
public imports and definition bodies. Preflight conservatively flags attribute commands
and requested this record.

## Old

The original local irreducibility command is verbatim:

```lean
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
```

## New

The local irreducibility commands are verbatim:

```lean
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CondensedRing.derivedPullIso CondensedRing.derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction CondensedRing.upperStar

attribute [local irreducible] scalarAdj sectionScalarRestriction scalarRestrictionPull
  scalarRestrictionPush scalarCoefficientPull
  ModuleRingedComparison.derivedPushforward
  scalarSectionPushComparison
```

No declaration signature or definition body changes. The only other item changes are
proofs, private proof imports and a local heartbeat setting with its explanation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Local elaboration settings for its proofs. |

`tools/downstream.py Sheaf.Paper.FlatCoefficientSquareNormalization --uses
flat_coefficient_square_normalization` reports zero downstream modules; its sole textual
use is the declaration in the item itself. The attributes are local, so importers inherit
no reducibility changes. No consumer adaptation is necessary. The new bridge modules
import earlier interfaces, not the item. No target meaning is changed.

## Status

landed 20261024T020139-L-2560514 2026-10-24 (merge of deliver/R9/Sheaf.Paper.FlatCoefficientSquareNormalization)
