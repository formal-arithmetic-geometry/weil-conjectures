# AlgebraicGeometry.derivedDirectImage_pasted_counit_normalization

## Reason

Restore the quarantined stage-3 item from its archived source. The current source
library defines `AlgebraicGeometry.derivedPullback` with `irreducible_def`, so Lean
rejects the archived command which sets `[local irreducible]` on it again. This is
the compiler error recorded in `coord/rework.tsv` for this item. Delete that one
redundant entry from the local attribute command. The statement, theorem proof,
private helpers, options and public import remain exactly as in the archive.

The upstream twin already makes this same adjustment. Its import closure contains
other upstream twins, so keep this module and its original public import, as
recorded in `coord/changes/retire-sheaf-twins-kept-20261020.tsv`. No upstream source
file is changed.

## Old

```lean
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Adjunction.comp
  derivedPullback Scheme.Modules.tensorPullback DerivedCategory.Qh
```

## New

```lean
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Adjunction.comp
  Scheme.Modules.tensorPullback DerivedCategory.Qh
```

This command is local. `derivedPullback` retains its existing irreducibility. All
public and private declaration signatures, proof bodies and imports are unchanged.
No definition is modified, and no target statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | unclaimed in current local claim records; quarantined | Imports all of this module and uses the private `counit_of_normalization`; that declaration is preserved verbatim. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit | unclaimed in current local claim records; quarantined | Uses `derivedDirectImage_pasted_counit_normalization`; that declaration is preserved verbatim. |

Both archived consumers were read. Their own redundant local `derivedPullback`
attribute entries are separate rework items. This change does not force any
consumer adaptation.

## Status

landed 20261020T150658-L-2571815 2026-10-20 (merge of deliver/P1/Sheaf.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization)
