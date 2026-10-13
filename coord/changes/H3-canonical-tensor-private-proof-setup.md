# AlgebraicGeometry.schemeCanonicalTensorShift_properties

## Reason

The static interface detector flags the added namespace-local variable, open and
local-instance commands needed to elaborate two proved private helpers. This is
proof setup, not a change to the existing theorem or to any definition. The record
makes the conservative classifier's warning reviewable. No consumer is adapted.

## Old

```lean
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
```

The original theorem signature is preserved verbatim in the delivery.

## New

Before the unchanged AlgebraicGeometry namespace, a
`DerivedCategory.IndependentTensorShift` namespace contains only two private,
proved lemmas. Its setup is:

```lean
universe v s
variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
attribute [local instance] commShift₂CurriedTensor
open DerivedCategory.IndependentTensorShift.TensorCommShift₂
```

The namespace closes before the public theorem. The local instance is scoped to
that namespace. No private declaration occurs in any public signature or definition,
and no exported instance or public theorem is altered. The new public right-unitor
lemma lives in a new module imported for proofs only.

## Users

`tools/downstream.py --uses AlgebraicGeometry.schemeCanonicalTensorShift_properties`
reports the following actual declaration users. All downstream statements keep
exactly their old meaning, because the original signature and tensor construction
are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties | H3 | Proof completed from proved exactness and the isolated unitor lemma; signature unchanged. |
| Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne | No adaptation; holder not needed | Uses the unchanged theorem signature; no edits needed. |

## Status

landed 20261013T134801-L-129634 2026-10-13 (merge of deliver/H3/Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties)
