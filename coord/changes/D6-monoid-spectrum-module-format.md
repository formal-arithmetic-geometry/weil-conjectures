# Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal module format

## Reason

The assigned spectrum theorem needs the existing affine universal-property theorem.
Both files still used the old Lean file format. A module cannot import the old
AffineMonoschemeHomUniversal file. Convert both to module files, preserving the
visibility of their existing imports and declarations. The affine dependency is unclaimed.

## Old

AffineMonoschemeHomUniversal began with these imports and had no module/public section:

```lean
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
import Mathlib.Topology.Sheaves.SheafCondition.Sites
```

MonoidSpectrumHomUniversal began with these imports and had no module/public section:

```lean
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
```

## New

Both files have `module` after the copyright and `@[expose] public section`
after the module docstring. Their preexisting imports are `public import`.
The assigned module adds private proof imports of AffineMonoschemeHomUniversal
and Mathlib.Topology.Sheaves.Skyscraper. No existing declaration signature,
attribute, definition body or theorem docstring changes. The dependency theorem
retains its preexisting sorry; the assigned theorem is proved from it.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal | unclaimed | module conversion only |
| Sheaf.AlgebraicGeometry.MonoidSpectrumHomUniversal | D6 | module conversion and proof |

`tools/downstream.py --uses` and direct-import searches found no preexisting
downstream modules for either module. The assigned module is the sole new
consumer of the converted dependency. Both compile together in dependency order.

## Status

landed 20261026T081435-L-1962160 2026-10-26 (merge of deliver/D6/Sheaf.AlgebraicGeometry.MonoidSpectrumHomUniversal)
