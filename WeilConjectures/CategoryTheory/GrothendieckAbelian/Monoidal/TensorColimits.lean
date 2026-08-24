/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!

# Compatibility of the tensor product of étale sheaves with colimits (sorried)

The K-flat left derivability structure requires the tensor product of the sheaf
category to interact well with the coproducts defining the tensor product of complexes
and with `ℤ`-indexed colimits. The instances of this file transport these hypotheses
from the coefficient category `A` to the categories of `A`-valued étale sheaves, for
the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`; the transports are
not yet formalized and are recorded with `sorry`.

## Sorried instances

- `AlgebraicGeometry.Etale.sheafHasTensor₄ObjExt`,
  `AlgebraicGeometry.Etale.sheafHasGoodTensor₁₂Tensor` and
  `AlgebraicGeometry.Etale.sheafHasGoodTensorTensor₂₃`: compatibility of the tensor
  product of graded étale sheaves with coproducts.
- `AlgebraicGeometry.Etale.sheafPreservesColimitsOfShapeCurriedTensorObj` and
  `AlgebraicGeometry.Etale.sheafPreservesColimitsOfShapeCurriedTensorFlipObj`:
  preservation of `ℤ`-indexed colimits by the tensor product of étale sheaves in each
  variable.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasTensor₄ObjExt
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasGoodTensor₁₂Tensor
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasGoodTensorTensor₂₃
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  sorry

/-- Preservation of `ℤ`-indexed colimits by the tensor product of étale sheaves in the
first variable, induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafPreservesColimitsOfShapeCurriedTensorObj
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf Y.smallEtaleTopology A)).obj X) :=
  sorry

/-- Preservation of `ℤ`-indexed colimits by the tensor product of étale sheaves in the
second variable, induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafPreservesColimitsOfShapeCurriedTensorFlipObj
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf Y.smallEtaleTopology A)).flip.obj X) :=
  sorry

end AlgebraicGeometry
