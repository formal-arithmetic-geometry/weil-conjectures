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
- `CategoryTheory.MonoidalClosed.twistedEvaluation`: the evaluation
  `X ⊗ ((ihom X).obj (𝟙_ C) ⊗ Z) ⟶ Z`, uncurried from the comparison map.

## Main statements

- `CategoryTheory.MonoidalClosed.curry_evaluation`: the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of
  the evaluation of an exact pairing of `Y` and `X` is an isomorphism.
- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom`: the comparison map is an
  isomorphism when `X` has a left dual.
- `CategoryTheory.MonoidalClosed.bijective_whiskerLeft_comp_twistedEvaluation`: when `X` has a
  left dual, morphisms `M ⟶ (ihom X).obj (𝟙_ C) ⊗ Z` correspond to morphisms `X ⊗ M ⟶ Z` through
  the twisted evaluation.

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

/-- The counit of `tensorLeftAdjunction Y X : tensorLeft X ⊣ tensorLeft Y` at `Z` is the composite
```
              α⁻¹                 ε_ Y X ▷ Z            λ_ Z
  X ⊗ (Y ⊗ Z) ───→ (X ⊗ Y) ⊗ Z ──────────→ 𝟙_ C ⊗ Z ─────→ Z.
```
-/
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

/-- If `Y` is a left dual of `X`, the comparison map is identified with `ihomObjIsoTensor`:
the square
```
                              ihomUnitTensorToIhom X Z
  (ihom X).obj (𝟙_ C) ⊗ Z ──────────────────────────→ (ihom X).obj Z
              │                                              │
  (ihomObjUnitIso Y X).hom ▷ Z               (ihomObjIsoTensor Y X Z).hom
              ↓                                              ↓
            Y ⊗ Z ═══════════════════════════════════════ Y ⊗ Z
```
commutes. -/
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

/-- If `Y` is a left dual of `X`, the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of the evaluation
`ε_ Y X : X ⊗ Y ⟶ 𝟙_ C` is the inverse of `ihomObjUnitIso Y X`. -/
theorem curry_evaluation (Y X : C) [ExactPairing Y X] :
    curry (ε_ Y X) = (ihomObjUnitIso Y X).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ C)
  rw [tensorLeftAdjunction_counit_app] at h₁
  dsimp only [ihom.ihom_adjunction_counit] at h₁
  rw [curry_eq_iff, uncurry_eq, ← h₁]
  simp only [ihomObjUnitIso, ihomObjIsoTensor, ihomIsoTensorLeft, Iso.trans_inv, Iso.app_inv,
    curriedTensor_obj_map, MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc X
    (((ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)).inv.app (𝟙_ C)),
    Iso.inv_hom_id_app]
  monoidal

instance isIso_curry_evaluation (Y X : C) [ExactPairing Y X] :
    IsIso (curry (ε_ Y X)) := by
  rw [curry_evaluation]
  infer_instance

/-- If `X` has a left dual, the comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z` is an
isomorphism. -/
theorem isIso_ihomUnitTensorToIhom (Y X : C) [ExactPairing Y X] (Z : C) :
    IsIso (ihomUnitTensorToIhom X Z) := by
  rw [ihomUnitTensorToIhom_eq Y X]
  infer_instance

/-- The *twisted evaluation* `X ⊗ ((ihom X).obj (𝟙_ C) ⊗ Z) ⟶ Z`,
```
                       α⁻¹                                 ev ▷ Z             λ
X ⊗ ([X, 𝟙] ⊗ Z) ─────────▶ (X ⊗ [X, 𝟙]) ⊗ Z ─────────▶ 𝟙_ C ⊗ Z ─────▶ Z
```
the uncurried form of `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`. -/
noncomputable def twistedEvaluation (X Z : C) : X ⊗ ((ihom X).obj (𝟙_ C) ⊗ Z) ⟶ Z :=
  (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom

lemma whiskerLeft_comp_twistedEvaluation (X : C) {M Z : C}
    (s : M ⟶ (ihom X).obj (𝟙_ C) ⊗ Z) :
    X ◁ s ≫ twistedEvaluation X Z = uncurry (s ≫ ihomUnitTensorToIhom X Z) := by
  rw [ihomUnitTensorToIhom, uncurry_natural_left, uncurry_curry, twistedEvaluation]

/-- If `X` has a left dual, the twisted evaluation induces a bijection between morphisms
`M ⟶ (ihom X).obj (𝟙_ C) ⊗ Z` and morphisms `X ⊗ M ⟶ Z`, `s ↦ (X ◁ s) ≫ ev`. -/
lemma bijective_whiskerLeft_comp_twistedEvaluation (Y X : C) [ExactPairing Y X] (M Z : C) :
    Function.Bijective (fun s : M ⟶ (ihom X).obj (𝟙_ C) ⊗ Z ↦
      X ◁ s ≫ twistedEvaluation X Z) := by
  have := isIso_ihomUnitTensorToIhom Y X Z
  have h : (fun s : M ⟶ (ihom X).obj (𝟙_ C) ⊗ Z ↦ X ◁ s ≫ twistedEvaluation X Z) =
      ((ihom.adjunction X).homEquiv _ _).symm ∘ (fun s ↦ s ≫ ihomUnitTensorToIhom X Z) := by
    ext s
    exact whiskerLeft_comp_twistedEvaluation X s
  rw [h]
  exact ((ihom.adjunction X).homEquiv _ _).symm.bijective.comp
    (asIso (ihomUnitTensorToIhom X Z)).homToEquiv.bijective

end MonoidalClosed

end CategoryTheory
