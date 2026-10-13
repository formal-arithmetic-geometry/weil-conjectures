# DerivedPullbackShiftedUnitIsoData import visibility

## Reason

`Mathlib.CategoryTheory.Triangulated.Functor` is used only in the proof of
`AlgebraicGeometry.exists_derivedPullback_shifted_unit_iso`. Making it private
keeps the module's public interface minimal while preserving its statement.

## Old

```lean
public import Mathlib.CategoryTheory.Triangulated.Functor
```

## New

```lean
import Mathlib.CategoryTheory.Triangulated.Functor
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData | unclaimed | imports this module; its own declarations do not use the private proof import |

## Status

landed 20261013T215614-L-902053 2026-10-13 (merge of deliver/U2/Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData)
