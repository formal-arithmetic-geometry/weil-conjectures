# AlgebraicGeometry.ProEtale.InternalDerivedClosedLocalization.derivedRestriction

## Reason

Repeated conversion between the native derived pullback and its inferred monoidal
instances caused kernel type-checking to expand geometric pullback. Store the existing
functor and its existing specified monoidal instance in a concrete shared data package.
The shared package first reduced the restriction helper's kernel time from about
32 seconds to 13.2 seconds. Explicitly generalizing its functor and monoidal field
then reduced kernel checking to 345 ms.
No source-library declaration changes. There is no existential choice in this construction.

## Old

```lean
abbrev derivedRestriction {Y : Scheme.{u}} (f : Y ⟶ X) :=
  monoidalUnderlying (CondensedRing.monoidal_leftDerivedUpperStar Λ.X f)
```

## New

```lean
abbrev derivedRestriction {Y : Scheme.{u}} (f : Y ⟶ X) :=
  (CondensedRing.nativeDerivedRestrictionData Λ f).functor
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalDerivedClosedLocalization | F7 | Same native functor and tensorator, projected from shared data; proof adapted in this packet. |

`tools/downstream.py Sheaf.Paper.InternalDerivedClosedLocalization --uses derivedRestriction`
reports no downstream modules and only the assigned module as a textual user. No other
module needs adaptation. A target's mathematical meaning is unchanged; the definition
representation is submitted for the independent reader's check under the stage-2 boundary.

## Status

landed 20261024T185251-L-3494252 2026-10-24 (merge of deliver/F7/Sheaf.Paper.InternalDerivedClosedLocalization)
