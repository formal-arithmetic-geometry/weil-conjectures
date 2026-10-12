# Sheaf.AlgebraicGeometry.StalkImageRange proof-only imports

## Reason

The exactness theorem and the Abelian image comparison are used only in the
proof of `AlgebraicGeometry.Scheme.stalk_image_inclusion_range`. They should
not be re-exported as part of this module's statement interface.

## Old

```lean
public import Sheaf.Algebra.Homology.ModuleStalkExact
public import Mathlib.CategoryTheory.Abelian.Images
```

## New

```lean
import Sheaf.Algebra.Homology.ModuleStalkExact
import Mathlib.CategoryTheory.Abelian.Images
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IdealModuleMultiplicationStalkRange | unclaimed | The theorem and all statement-level names remain available; it compiles unchanged. |

## Status

landed 20261012T184352-L-4022838 2026-10-12 (merge of deliver/V1/Sheaf.AlgebraicGeometry.StalkImageRange)
