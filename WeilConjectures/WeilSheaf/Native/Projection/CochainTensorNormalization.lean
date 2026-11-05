/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.OrdinaryTensorNormalization

/-! # The tensor bifunctor of cochain complexes -/

@[expose] public noncomputable section

universe u v
open CategoryTheory Abelian MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]

/-- The tensor bifunctor of complexes is the total extension of the coefficient tensor. -/
lemma projection_curriedTensorCochain_eq :
    curriedTensor (CochainComplex C ℤ) = (curriedTensor C).map₂CochainComplex := rfl

end CategoryTheory
