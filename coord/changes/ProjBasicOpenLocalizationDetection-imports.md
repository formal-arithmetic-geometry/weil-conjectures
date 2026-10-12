# Sheaf.AlgebraicGeometry.ProjBasicOpenLocalizationDetection imports

## Reason

The theorem uses Proj basic opens and ordinary localization; it never uses the twisting
sheaf constructions. Replace the unused public twisting-sheaf import with the basic Proj
module supplying the types in the theorem's signature. No declaration, definition, target
statement, or mathematical meaning changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Module.LocalizedModule.Basic
```

## New

```lean
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjTwistBasicOpenFractions | unclaimed | It already publicly imports WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules itself. It imports the changed module only for the unchanged detection theorem. No adaptation is needed. |

This is the only direct importing module found by searching the source import declarations.
Its transitive consumers retain the twisting-sheaf import through its own public import.
No target definition changes, so no target meaning review is reopened.

## Status

landed 20261012T135302-L-1685504 2026-10-12 (merge of deliver/P3/Sheaf.AlgebraicGeometry.ProjBasicOpenLocalizationDetection)
