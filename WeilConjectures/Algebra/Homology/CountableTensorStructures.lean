/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Tensor structures from countable coproducts

Countable sums give the signed direct-sum totalization, using Mathlib's graded-object and
homological-complex monoidal constructions.

## References

* Stacks Project, Tag 0G6E (signed direct-sum totalization)
-/

@[expose] public section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/-- Tensoring on either side preserves coproducts indexed by any countable set. -/
class TensorPreservesCountableCoproducts (C : Type u) [Category.{v} C]
    [MonoidalCategory C] : Prop where
  /-- Preservation by left tensoring, including the empty coproduct. -/
  left (I : Type) [Countable I] (X : C) :
    PreservesColimitsOfShape (Discrete I) (tensorLeft X)
  /-- Preservation by right tensoring, including the empty coproduct. -/
  right (I : Type) [Countable I] (X : C) :
    PreservesColimitsOfShape (Discrete I) (tensorRight X)

attribute [instance] TensorPreservesCountableCoproducts.left
  TensorPreservesCountableCoproducts.right

namespace CountableTensorStructures

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [TensorPreservesCountableCoproducts C]

/-- Countable sums give the binary graded tensors used in totalization. -/
noncomputable instance hasTensor (X Y : GradedObject ℤ C) : X.HasTensor Y :=
  inferInstance

/-- Tensoring the first two factors commutes with the sum defining their tensor. -/
noncomputable instance goodTensorLeft (X Y Z : GradedObject ℤ C) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  fun _ _ ↦ inferInstance

/-- Tensoring the last two factors commutes with their defining sum. -/
noncomputable instance goodTensorRight (X Y Z : GradedObject ℤ C) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  fun _ _ ↦ inferInstance

/-- The triple-sum comparison needed by the pentagon uses a countable index set. -/
noncomputable instance tensorFour (W X Y Z : GradedObject ℤ C) :
    GradedObject.HasTensor₄ObjExt W X Y Z :=
  fun _ _ ↦ inferInstance

end CountableTensorStructures
end CategoryTheory

namespace CategoryTheory.CountableTensorStructures

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [TensorPreservesCountableCoproducts C]

/-- The standard signed direct-sum monoidal structure on integer cochain complexes. -/
noncomputable instance monoidal : MonoidalCategory (CochainComplex C ℤ) :=
  HomologicalComplex.monoidalCategory C (.up ℤ)

end

end CategoryTheory.CountableTensorStructures
