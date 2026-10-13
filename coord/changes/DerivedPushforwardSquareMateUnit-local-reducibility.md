# DerivedPushforwardSquareMateUnit local reducibility

## Reason

The preflight classifies added attribute commands conservatively as interface
changes, including local irreducibility attributes. The proof uses local
irreducibility to keep right-derived functors, their units, Qh, derivedPullback
and the normalized comparison folded during elaboration. These attributes are
local to the file and do not change downstream definitions or statements.
This record documents the flagged commands; there is no interface change.

## Old

No local irreducibility commands. The existing theorem signature is unchanged.

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  derivedPullback DerivedCategory.Qh
attribute [local irreducible] schemeNormalizedDirectImageCompIso
```

The existing theorem signature is byte-for-byte unchanged. No target changes
meaning, and no target's statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | V3 | Local proof elaboration only; unchanged public signature. |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | not identified in local claims; not adapted | Sole direct importer and sole direct textual user; unchanged statement and definitions. |

Read-only tools/downstream.py reports 343 transitive downstream modules and
exactly these two textual users of the declaration. None is adapted: local
attributes are not exported, and every downstream statement has exactly the
same definitions and theorem signature as before.

## Status

landed 20261013T201811-L-3977748 2026-10-13 (merge of deliver/V3/Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit)
