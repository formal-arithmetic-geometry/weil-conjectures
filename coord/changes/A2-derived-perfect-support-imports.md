# Import boundary of GrothendieckDerivedPerfectWellGeneratorsSupport

## Reason

The support construction is now completely proved by bounded complexes and bounded roofs.
It does not use the compact-generator telescope. Its direct consumer does use the telescope
and previously obtained it from the support module's public import. Move that import to
the actual consumer. Also import ObjectProperty.Shift in place of the larger triangulated
subcategory module, since only shift stability occurs in the support statement.

No definition or existing declaration signature changes. No target is restated or weakened.

## Old

In `Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGeneratorsSupport`:

```lean
public import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects
public import Mathlib.CategoryTheory.Triangulated.Subcategory
```

The consumer had:

```lean
import Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGeneratorsSupport
```

## New

The support module removes the compact-generator import and uses:

```lean
public import Mathlib.CategoryTheory.ObjectProperty.Shift
```

The consumer has:

```lean
import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects
import Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGeneratorsSupport
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGeneratorsSupport | A2 | Main proof completed; unused telescope import removed; shift dependency narrowed. |
| Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGenerators | unclaimed | One ordinary import added to restore the existing telescope call. |

`tools/downstream.py ... --uses compactGenerators_buildObjects` reports the consumer as
the only actual user below the support module. It is also the sole direct importer of the
support module. Its import of support is ordinary, so support's imported names are not
reexported through it to the remaining downstream modules. All public theorem types in
both delivered modules are unchanged, and their joint compile succeeds.

The original consumer against the changed support failed with unknown identifier
`compactGenerators_buildObjects` at line 55 and the resulting `rcases` error at line 54.
The adapted consumer compiles. No other consumer line is changed; the unit's compact-generator
telescope remains in use at its original call.

## Status

landed 20261018T011152-L-2723149 2026-10-18 (merge of deliver/A2/Sheaf.CategoryTheory.GrothendieckDerivedPerfectWellGeneratorsSupport)
