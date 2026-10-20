# Sheaf.CategoryTheory.BraidedSheafTensorGenerators proof scopes

## Reason

Complete the two existing proofs. The static preflight flags added `variable`, `open`,
`universe`, and `attribute` commands conservatively as a possible interface change.
All added commands are within `section BraidedTensorProof`, which ends before the
existing namespace ends. The added instance attributes are local. Every added helper
is private and proved. The existing public structure, theorem signatures, declaration
attributes, and public imports are unchanged. The one added import is proof-only.

## Old

The two existing signatures, verbatim (each previously had a `sorry` proof):

```lean
theorem nonempty_braidedTensorGenerators
    {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A] : Nonempty (BraidedTensorGenerators J A)

theorem nonempty_braidedTensorGenerators_smallSkeleton
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A] :
    Nonempty (BraidedTensorGenerators
      (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A)
```

There was no `BraidedTensorProof` section or private `Retensor` namespace.

## New

The same signatures, verbatim (each now has a complete proof):

```lean
theorem nonempty_braidedTensorGenerators
    {C : Type w} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify J A] : Nonempty (BraidedTensorGenerators J A)

theorem nonempty_braidedTensorGenerators_smallSkeleton
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (A : Type uA) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
    [HasWeakSheafify (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A] :
    Nonempty (BraidedTensorGenerators
      (((skeletonEquivalence (SmallModel.{w} C)).functor ⋙
      (equivSmallModel.{w} C).inverse).inducedTopology J) A)
```

The added proof scope starts with these commands:

```lean
section BraidedTensorProof

open CategoryTheory.Category
open scoped CategoryTheory.MonoidalClosed

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
```

It contains private helpers for transport of monoidal coherence, local instances, and
both proofs. The `Retensor` namespace contains its own variables. After that namespace
closes, `attribute [local instance] Retensor.copyCategory` makes the private copy's
category available in this section. The section ends after the small-skeleton theorem.
These commands do not install global instances or modify downstream declarations.
The public theorem types were compared verbatim and inspected by `#check` on the server.

## Users

`tools/downstream.py Sheaf.CategoryTheory.BraidedSheafTensorGenerators --uses
BraidedTensorGenerators nonempty_braidedTensorGenerators
nonempty_braidedTensorGenerators_smallSkeleton` reports no declaration-name user outside
the item module. There are 556 transitive importers in the current snapshot; none uses
these names textually, and no import or signature they receive is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BraidedSheafTensorGenerators | A2 | Both proofs completed; all original signatures and public imports preserved. |

No consumer adaptation is required or included. The independent reader can verify that
all added helpers are private and all added instance attributes are local.

## Status

landed 20261020T151210-L-2645917 2026-10-20 (merge of deliver/A2/Sheaf.CategoryTheory.BraidedSheafTensorGenerators)
