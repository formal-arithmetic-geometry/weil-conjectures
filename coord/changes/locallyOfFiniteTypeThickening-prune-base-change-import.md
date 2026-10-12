# LocallyOfFiniteTypeThickening: remove unused public import

## Reason

The proof and statement only need Mathlib pullbacks, finite type, and the project's
thickening definition. BaseChangeConventions is unnecessary. Removing its public
import prunes its proof dependencies from this module. The existing theorem's
signature and visibility are identical. Both new helpers are private and proved.

## Old

```lean
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
```

## New

The unused import is removed. The proof adds only a private import:

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Flat
```

The existing private import of Sheaf.Algebra.FiniteTypeLiftNilpotent stays.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteThickeningCartesian | unclaimed in this checkout | Sole direct importer; already has its own public import of BaseChangeConventions, so all its public dependencies and statements remain available unchanged. No adaptation is needed. |

`tools/downstream.py` finds 185 transitive importers. Each path goes through the
sole direct importer above. Its independent public BaseChangeConventions import
preserves that visibility throughout those paths. No definition or theorem type
changes. No source module is adapted by this delivery.

## Status

landed 20261012T144103-L-2092166 2026-10-12 (merge of deliver/E2/Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeThickening)
