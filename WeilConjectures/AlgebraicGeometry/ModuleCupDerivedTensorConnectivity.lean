/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-! # Nonpositive connectivity of derived tensor

## References

* Stacks Project, Tag 06YH.
-/

@[expose] public section

universe w v u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{w} C]

/-- The tensor of degree-zero objects has no positive cohomology (Stacks, Tag 06YH). -/
theorem moduleCup_derived_tensor_connectivity (F G : C) :
    (((singleFunctor C 0).obj F) ⊗ ((singleFunctor C 0).obj G)).IsLE 0 := by
  simpa using isLE_tensor ((singleFunctor C 0).obj F) ((singleFunctor C 0).obj G) 0 0

end DerivedCategory
