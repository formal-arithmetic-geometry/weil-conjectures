# CategoryTheory.augmentedScalarRoosResolution proof context

## Reason

The complete proof adds section variables for private generic-category helpers and
sets elaboration options for dependent cone/product morphisms. The static interface
checker includes these commands in its interface comparison and requests this record.
No public declaration signature, definition body, attribute, or public import changes.
The extra section variables are closed before the public theorem. The options control
elaboration of this file; they add no mathematical hypotheses or axioms.

## Old

The original non-declaration command context, verbatim after comment removal:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v uB vB w t r
open CategoryTheory CategoryTheory.Limits Opposite
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
variable [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
variable (Z : AlgebraicGeometry.Scheme.{t})
open AugmentedScalarRoos
set_option backward.isDefEq.respectTransparency true
```

## New

The delivered non-declaration command context, verbatim after comment removal:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v uB vB w t r
open CategoryTheory CategoryTheory.Limits Opposite
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
variable [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
variable (Z : AlgebraicGeometry.Scheme.{t})
open AugmentedScalarRoos
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
variable [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A] {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
```

All public declarations are identical except for the completed theorem proof.
Private helpers are fully proved and add no exported instances or attributes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.AugmentedScalarRoosResolution --uses
augmentedScalarRoosResolution` reports zero downstream modules and only the item's
own declaration as a textual use. The node remains needed by its unfinished parent;
this is not a withdrawal. No consumer adaptation or target statement change is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.AugmentedScalarRoosResolution | V3 | Sole hole filled; private proof context added; public API unchanged. |

## Status

landed 20261023T135712-L-2960301 2026-10-23 (merge of deliver/V3/Sheaf.CategoryTheory.AugmentedScalarRoosResolution)
