/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Tensor structures from countable coproducts

Source: Stacks Project, derived.tex, Tag 0G6E, signed direct-sum totalization;
Mathlib's graded-object and homological-complex monoidal constructions.
(blueprint: def-sfb-countable-tensor-structures)
-/

@[expose] public section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/-- Tensoring on either side preserves coproducts indexed by any countable set.
Source: Stacks Project, derived.tex, Tag 0G6E, totalization;
preservation assumption of the owning exact-equivalence node
(blueprint: def-sfb-countable-tensor-structures).
Countable sets in larger universes have equivalent representatives in `Type`. -/
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

/-- Countable sums give the binary graded tensors used in totalization.
Source: Mathlib's coproduct construction, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance hasTensor (X Y : GradedObject ℤ C) : X.HasTensor Y :=
  inferInstance

/-- Tensoring the first two factors commutes with the sum defining their tensor.
Source: Mathlib's graded associator construction, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance goodTensorLeft (X Y Z : GradedObject ℤ C) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  fun _ _ ↦ inferInstance

/-- Tensoring the last two factors commutes with their defining sum.
Source: Mathlib's graded associator construction, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance goodTensorRight (X Y Z : GradedObject ℤ C) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  fun _ _ ↦ inferInstance

/-- The triple-sum comparison needed by the pentagon uses a countable index set.
Source: Mathlib's graded pentagon construction, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance tensorFour (W X Y Z : GradedObject ℤ C) :
    GradedObject.HasTensor₄ObjExt W X Y Z :=
  fun _ _ ↦ inferInstance

/-- The standard signed direct-sum monoidal structure on integer cochain complexes.
Source: Mathlib `HomologicalComplex.monoidalCategory`, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance monoidal : MonoidalCategory (CochainComplex C ℤ) :=
  HomologicalComplex.monoidalCategory C (.up ℤ)

/-- The standard Koszul braiding, with summand map `(-1)^(pq)` times the base braiding.
Source: `CochainComplex.Monoidal.braidedCategory`, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance braided [BraidedCategory C] : BraidedCategory (CochainComplex C ℤ) :=
  CochainComplex.Monoidal.braidedCategory

end CountableTensorStructures
end CategoryTheory
