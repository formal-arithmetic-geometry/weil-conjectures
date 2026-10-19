# AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible elaboration attributes

## Reason

The proof of `closedSupport_constructible` uses the existing derived-functor interfaces
whose elaboration unfolds a large internal-Hom and coefficient-pullback expression. The
sandbox proof exceeded the single-file elaboration budget until these existing constants
were marked locally irreducible. The attributes are local to this module and preserve all
public declarations and theorem statements; the record is required because the delivery
checker classifies attribute commands as observable interface changes.

## Old

No local reducibility attribute command existed in the original module. The existing
`open` commands and namespace declaration were adjacent:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
```

## New

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.rightDerivedFunctor Sheaf.monoidalCategory
```

All five entries are local attributes only. They do not introduce definitions,
instances, notation, or declarations and do not alter any statement.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedSupportConstructible | A7 | Uses the local attributes to keep the completed proof within the single-file elaboration budget. |

The required `tools/downstream.py Sheaf.Paper.ClosedSupportConstructible --uses
AlgebraicGeometry.ProEtale.CondensedRing.closedSupport_constructible` search lists only
the item itself as a textual declaration-name user. The import graph has 230 downstream
modules, but all exported definitions, signatures, public imports and visibility are
unchanged. The attribute scope ends in this module; no consumer adaptation or target
statement review is required. No mathematical definition changes.

## Status

landed 20261019T231033-L-541470 2026-10-19 (merge of deliver/A7/Sheaf.Paper.ClosedSupportConstructible)
