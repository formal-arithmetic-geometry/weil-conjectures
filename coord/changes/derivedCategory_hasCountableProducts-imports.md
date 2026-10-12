# CategoryTheory.derivedCategory_hasCountableProducts (imports)

## Reason

The existence statement needs DerivedCategory.Basic and GrothendieckAxioms.Basic.
HomologySequence and HomologicalComplexLimits are unnecessary public imports of the item.
The proof obtains its termwise-cone theorem from a plain import of the new core module.
No existing declaration signature, visibility, definition or target statement changes.

## Old

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.CategoryTheory.LocalizationHomColimit
```

## New

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsCore
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts | unclaimed in local claim records | Sole direct importer and sole downstream textual user of the declaration; imports both removed Mathlib modules itself. Its original source compiles unchanged against the delivery overlay. Every further downstream module sees the same public imports of this importer, so its interface is unchanged. |

No adaptation is required. `tools/downstream.py --uses` reports only this user, apart
from the defining module, though there are 732 transitive importers. None of their
statements or definitions changes meaning.

## Status

landed 20261012T184246-L-3998284 2026-10-12 (merge of deliver/C3/Sheaf.CategoryTheory.Triangulated.DerivedCountableProductsExistence)
