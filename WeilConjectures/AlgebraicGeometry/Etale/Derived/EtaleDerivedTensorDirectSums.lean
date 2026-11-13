/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement

/-!
# Derived tensor products of étale sheaves preserve direct sums
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Tensoring on either side with an arbitrary unbounded derived étale sheaf preserves
set-indexed direct sums, including the empty sum. -/
theorem derivedTensor_preservesDirectSums (Λ : Type (u + 1)) [CommRing Λ]
    (T : Scheme.{u}) (A : DerivedCategoryModule Λ T) :
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).flip.obj A)) := by
  -- The existing tensor--Hom adjunction avoids unfolding the derived monoidal structure.
  have h (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj A) :=
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) A).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  refine ⟨h, fun I ↦ ?_⟩
  have := h I
  exact preservesColimitsOfShape_of_natIso
    ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) T).app A)

end AlgebraicGeometry.Etale
