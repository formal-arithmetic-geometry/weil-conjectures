# AlgebraicGeometry.schemeCanonicalTensorShift_rightUnitor

## Reason

The static interface detector flags namespace-local variables, opens and local-instance
commands used to elaborate three fully proved private helpers. They establish the
representative calculation, transport by an isomorphism, and extension to all derived
objects. The setup is confined to private proof code; the existing public theorem signature,
public imports and all shared definitions are unchanged. No consumer is adapted.

## Old

```lean
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
```

## New

```lean
universe u w v s
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits MonoidalCategory
namespace DerivedCategory.IndependentTensorShift
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
attribute [local instance] commShift₂CurriedTensor
```

Both occurrences of the local instance are confined to this namespace, which closes
before the existing public theorem. The transport helper is private as well. No private
helper occurs in a public signature or a public definition. No new global instance is added.

## Users

`tools/downstream.py --uses AlgebraicGeometry.schemeCanonicalTensorShift_rightUnitor`
finds the following declaration users. Both retain their signatures and meaning.
The conservative detector reports only commands, not a changed declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor | U4 | Proof completed; signature unchanged. |
| Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftProperties | unclaimed | Uses the unchanged theorem; no adaptation needed. |

## Status

landed 20261013T150355-L-811021 2026-10-13 (merge of deliver/U4/Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor)
