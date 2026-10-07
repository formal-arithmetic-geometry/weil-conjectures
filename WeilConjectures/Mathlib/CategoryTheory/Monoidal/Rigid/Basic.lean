/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!

# Dualizable and invertible objects of a monoidal category

`CategoryTheory.HasRightDual` is a class carrying a right dual as *data*. This file records
the corresponding *property*, `CategoryTheory.IsDualizable X`, that some right dual exists,
together with the stronger property `CategoryTheory.IsInvertible X` that `X` admits a
tensor inverse.

## Main definitions

- `CategoryTheory.IsDualizable`: `X` admits a right dual.
- `CategoryTheory.IsInvertible`: `X` admits a tensor inverse.
- `CategoryTheory.MonoidalClosed.ihomIsoTensorLeft`: for an exact pairing of `Y` and `X`, the
  internal hom `ihom X` is `Y ⊗ -`.
- `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`: the canonical comparison map
  `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom`: the comparison map is an
  isomorphism when `X` has a left dual.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- An object `X` of a monoidal category is *dualizable* if it admits a right dual, that is,
an object `Xᘁ` together with an exact pairing `X ⊗ Xᘁ ⟶ 𝟙_ C`, `𝟙_ C ⟶ Xᘁ ⊗ X`.

Unlike `CategoryTheory.HasRightDual`, which carries the dual as data, this is a `Prop`. -/
def IsDualizable (X : C) : Prop :=
  Nonempty (HasRightDual X)

theorem isDualizable_of_hasRightDual (X : C) [HasRightDual X] : IsDualizable X :=
  ⟨inferInstance⟩

theorem isDualizable_unit : IsDualizable (𝟙_ C) :=
  isDualizable_of_hasRightDual _

theorem IsDualizable.tensorObj {X Y : C} (hX : IsDualizable X) (hY : IsDualizable Y) :
    IsDualizable (X ⊗ Y) := by
  obtain ⟨_⟩ := hX
  obtain ⟨_⟩ := hY
  exact ⟨hasRightDualTensor⟩

/-- An object `X` of a monoidal category is *invertible* if it admits a tensor inverse, that
is, an object `Y` with `X ⊗ Y ≅ 𝟙_ C`. The Tate twists of the `ℓ`-adic formalism are the
motivating example. -/
def IsInvertible (X : C) : Prop :=
  ∃ Y, Nonempty (X ⊗ Y ≅ 𝟙_ C)

theorem isInvertible_unit : IsInvertible (𝟙_ C) :=
  ⟨𝟙_ C, ⟨λ_ _⟩⟩

theorem tensorLeftAdjunction_counit_app (Y X : C) [ExactPairing Y X] (Z : C) :
    (tensorLeftAdjunction Y X).counit.app Z = (α_ _ _ _).inv ≫ ε_ Y X ▷ Z ≫ (λ_ Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

namespace MonoidalClosed

variable [MonoidalClosed C]

/-- If `Y` is a left dual of `X`, that is, `Y` and `X` form an exact pairing, then the internal
hom `ihom X` of a monoidal closed category is tensoring on the left with `Y`: both are right
adjoint to `X ⊗ -`. -/
noncomputable def ihomIsoTensorLeft (Y X : C) [ExactPairing Y X] : ihom X ≅ tensorLeft Y :=
  (ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)

/-- If `Y` is a left dual of `X`, then `(ihom X).obj Z ≅ Y ⊗ Z`. -/
noncomputable def ihomObjIsoTensor (Y X : C) [ExactPairing Y X] (Z : C) :
    (ihom X).obj Z ≅ Y ⊗ Z :=
  (ihomIsoTensorLeft Y X).app Z

/-- If `Y` is a left dual of `X`, then the internal dual `(ihom X).obj (𝟙_ C)` is `Y`. -/
noncomputable def ihomObjUnitIso (Y X : C) [ExactPairing Y X] : (ihom X).obj (𝟙_ C) ≅ Y :=
  ihomObjIsoTensor Y X (𝟙_ C) ≪≫ ρ_ Y

/-- The canonical comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`: the transpose of
`X ⊗ ((ihom X).obj (𝟙_ C) ⊗ Z) ≅ (X ⊗ (ihom X).obj (𝟙_ C)) ⊗ Z ⟶ 𝟙_ C ⊗ Z ≅ Z`, built from
the evaluation `X ⊗ (ihom X).obj (𝟙_ C) ⟶ 𝟙_ C`. -/
noncomputable def ihomUnitTensorToIhom (X Z : C) : (ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z :=
  curry ((α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom)

theorem ihomUnitTensorToIhom_eq (Y X : C) [ExactPairing Y X] (Z : C) :
    ihomUnitTensorToIhom X Z = (ihomObjUnitIso Y X).hom ▷ Z ≫ (ihomObjIsoTensor Y X Z).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ C)
  have h₂ := (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) Z
  rw [tensorLeftAdjunction_counit_app] at h₁ h₂
  dsimp only [ihom.ihom_adjunction_counit] at h₁ h₂
  simp only [curriedTensor_obj_map] at h₁ h₂
  simp only [ihomUnitTensorToIhom, curry_eq_iff, uncurry_eq, ihomObjUnitIso, ihomObjIsoTensor,
    ihomIsoTensorLeft, Iso.trans_hom, Iso.app_inv, Adjunction.rightAdjointUniq_inv_app,
    Iso.app_hom]
  rw [← h₁, MonoidalCategory.whiskerLeft_comp_assoc, h₂]
  monoidal

/-- If `X` has a left dual, the comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z` is an
isomorphism. -/
theorem isIso_ihomUnitTensorToIhom (Y X : C) [ExactPairing Y X] (Z : C) :
    IsIso (ihomUnitTensorToIhom X Z) := by
  rw [ihomUnitTensorToIhom_eq Y X]
  infer_instance

end MonoidalClosed

end CategoryTheory
