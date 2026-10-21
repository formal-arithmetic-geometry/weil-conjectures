# Sheaf.Algebra.Homology.DerivedTensorTruncationWindow proof elaboration scope

## Reason

The delivery restores the quarantined item and proves its unchanged theorem. The
preflight requests a change record for added section commands and local attributes.
This record documents those commands; no existing statement, public import, definition body,
public instance, or persistent attribute is changed.

The private helpers use the generic derived tensor, so their section opens monoidal
notation and binds its ambient abelian monoidal category explicitly. The main proof
needs larger instance synthesis and controlled elaboration transparency. Local
irreducibility prevents expansion of the universal-property tensor and counit;
the proof uses their comparison APIs. These changes affect elaboration in this file.

## Old

The original top-level elaboration commands, verbatim:

```lean
set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules
```

The original theorem's existing scoped attribute remains verbatim:

```lean
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
```

There was no generic helper section or local irreducibility attribute.

## New

The new top-level elaboration commands, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

section Generic

open CategoryTheory.Pretriangulated MonoidalCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w} A]

variable [∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W]
```

The private K-flatness bridge omits assumptions it does not use, verbatim:

```lean
omit [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w} A]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W] in
```

After the three proved private helper theorems the section closes. The subsequent
namespace-local commands are verbatim:

```lean
end Generic

namespace SheafOfModules

-- Use the tensor and counit APIs without unfolding their universal-property choices.
attribute [local irreducible] wfSiteDerivedTensor DerivedMonoidal.bifunctor
  DerivedMonoidal.counit
```

The original scoped attribute and complete public theorem signature are unchanged.
The section variables occur only in the proved private helpers. The new opens,
options and local attributes do not add hypotheses or alter the theorem or any
importer's elaboration environment. There is no target definition change.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.DerivedTensorTruncationWindow
--uses SheafOfModules.isIso_derivedTensor_truncationWindow --allow-missing`
reports zero downstream modules and zero current source users. A separate source
search of `lean/Sheaf`, `lean/WeilConjectures`, and quarantined `Sheaf` modules
finds only the item's archive. Its DAG attachment and parent dependencies remain;
no withdrawal is proposed, and no consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | E2 | Restored; proof and private helper elaboration only; signature unchanged. |

## Status

landed 20261021T061014-L-1683930 2026-10-21 (merge of deliver/E2/Sheaf.Algebra.Homology.DerivedTensorTruncationWindow)
