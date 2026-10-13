# AlgebraicGeometry.supportedOpen_tensor_directImage_comparisons

## Reason

The static interface checker conservatively flags the added universe, open-scope,
options and local instance commands. These commands let the fully proved private
support/restriction glue elaborate across independent localization universes.
No public statement, definition, visibility or public import changes. The local
attribute declarations are scoped to this module's namespace and affect only proof
elaboration; no new global instance or elaboration attribute is exported.

## Old

Original elaboration commands, verbatim:

```lean
universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry
```

The theorem signature in `lean/Sheaf/AlgebraicGeometry/SupportedOpenTensorDirectImageComparisons.lean`
is unchanged.

## New

```lean
universe u w wO

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The extra wO is used only by private helpers. Existing declaration binders,
universes, statements and visibility stay identical, as confirmed by
`stage3_delivery.diff_module`: `statement_changed = []`, `public_added = []`.
No target or the definition of any target's objects changes.

## Users

`tools/downstream.py` finds 413 transitive importers, with one external textual
user of the theorem. All retain the same public interface. None needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperSupportDerivedProjectionFormula | unclaimed | No change: same theorem signature and public imports; only its dependency proof is completed. |
| Sheaf.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons | K2 | Fully proved private glue and local proof elaboration commands. |

No modules held by another group are edited. There are no forced adaptations.

## Status

landed 20261013T113346-L-3185422 2026-10-13 (merge of deliver/K2/Sheaf.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons)
