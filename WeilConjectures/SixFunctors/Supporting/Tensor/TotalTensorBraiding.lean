/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalTensor
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Koszul braiding with a stable signed-total source and target

This is the existing native braiding, exposed directly on the shared total functor.
Source: Stacks 0FPQ and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace WeilConjectures

/-- The native Koszul braiding between the shared signed total tensor objects.
The construction is unchanged; the explicit object types avoid unfolding the
monoidal structure on complexes in every consumer.
Source: Stacks 0FPQ (blueprint: def-sf-total-tensor-braiding). -/
@[irreducible] def totalTensorBraiding
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
    [HasColimitsOfSize.{0, 0} C]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (P Q : CochainComplex C ℤ) :
    (finiteScalarRepresentativeTotalTensor C).obj (P, Q) ≅
      (finiteScalarRepresentativeTotalTensor C).obj (Q, P) :=
  CochainComplex.Monoidal.braiding P Q

end WeilConjectures
