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
- `CategoryTheory.exactPairingOfTensorIso`: the exact pairing of an object with a two-sided
  tensor inverse.
- `CategoryTheory.tensorLeftEquivalence`, `CategoryTheory.tensorRightEquivalence`: tensoring
  with an object with a two-sided tensor inverse is an equivalence.
- `CategoryTheory.MonoidalClosed.ihomIsoTensorLeft`: for an exact pairing of `Y` and `X`, the
  internal hom `ihom X` is `Y ⊗ -`.
- `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`: the canonical comparison map
  `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`.

## Main statements

- `CategoryTheory.isDualizable_of_tensorIso`: an object with a two-sided tensor inverse is
  dualizable.
- `CategoryTheory.MonoidalClosed.curry_evaluation`: the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of
  the evaluation of an exact pairing of `Y` and `X` is an isomorphism.
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

/-- Two morphisms into the unit can be applied in either order: `f ⊗ g` computed as
`f ▷ B` followed by `g`, or as `A ◁ g` followed by `f`. -/
lemma whiskerRight_comp_leftUnitor_hom_comp {A B : C} (f : A ⟶ 𝟙_ C) (g : B ⟶ 𝟙_ C) :
    f ▷ B ≫ (λ_ B).hom ≫ g = A ◁ g ≫ (ρ_ A).hom ≫ f := by
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, ← rightUnitor_naturality,
    unitors_equal]

/-- If `X ⊗ Y ≅ 𝟙_ C`, then `- ▷ X` is injective on morphisms. -/
lemma whiskerRight_injective_of_tensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) {Z Z' : C}
    {f g : Z ⟶ Z'} (h : f ▷ X = g ▷ X) : f = g := by
  have key (k : Z ⟶ Z') : k = (ρ_ Z).inv ≫ Z ◁ e.inv ≫ (α_ Z X Y).inv ≫ (k ▷ X) ▷ Y ≫
      (α_ Z' X Y).hom ≫ Z' ◁ e.hom ≫ (ρ_ Z').hom := by
    rw [← whiskerRight_tensor_assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
      e.inv_hom_id, whiskerLeft_id, Category.id_comp, rightUnitor_naturality,
      Iso.inv_hom_id_assoc]
  rw [key f, key g, h]

/-- An object `X` with a two-sided tensor inverse `Y`, `X ⊗ Y ≅ 𝟙_ C ≅ Y ⊗ X`, forms an exact
pairing with `Y`. The coevaluation is the inverse of `X ⊗ Y ≅ 𝟙_ C`; the evaluation is
`Y ⊗ X ≅ 𝟙_ C` corrected by an automorphism of `X` so that the first zigzag identity holds,
and the second zigzag identity then follows, since `- ▷ X` is injective. -/
@[instance_reducible]
noncomputable def exactPairingOfTensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    ExactPairing X Y :=
  let φ : X ⟶ X := (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ e'.hom ≫ (ρ_ X).hom
  let ε : Y ⊗ X ⟶ 𝟙_ C := Y ◁ inv φ ≫ e'.hom
  have zig : (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = 𝟙 X := by
    have : (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = inv φ ≫ φ := by
      simp only [ε, φ, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]
    rw [this, IsIso.inv_hom_id]
  have zag : (ρ_ Y).inv ≫ Y ◁ e.inv ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom = 𝟙 Y := by
    apply whiskerRight_injective_of_tensorIso e
    rw [id_whiskerRight, ← cancel_mono ε, Category.id_comp]
    calc _ = (ρ_ Y).inv ▷ X ≫ (Y ◁ e.inv) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom ≫
          ε ▷ (Y ⊗ X) ≫ (λ_ (Y ⊗ X)).hom ≫ ε := by monoidal
      _ = (ρ_ Y).inv ▷ X ≫ (Y ◁ e.inv) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom ≫
          (Y ⊗ X) ◁ ε ≫ (ρ_ (Y ⊗ X)).hom ≫ ε := by
        rw [whiskerRight_comp_leftUnitor_hom_comp]
      _ = Y ◁ ((λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom) ≫ ε := by
        monoidal
      _ = ε := by rw [zig, whiskerLeft_id, Category.id_comp]
  { coevaluation' := e.inv
    evaluation' := ε
    coevaluation_evaluation' := by
      rw [← cancel_epi (ρ_ Y).inv, ← cancel_mono (λ_ Y).hom]
      simpa using zag
    evaluation_coevaluation' := by
      rw [← cancel_epi (λ_ X).inv, ← cancel_mono (ρ_ X).hom]
      simpa using zig }

/-- An object with a two-sided tensor inverse is dualizable. -/
theorem isDualizable_of_tensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    IsDualizable X :=
  letI := exactPairingOfTensorIso e e'
  ⟨⟨Y⟩⟩

/-- Tensoring on the left with an object `X` with a two-sided tensor inverse `Y` is an
equivalence, with inverse the tensor product with `Y`. -/
@[simps! functor inverse]
noncomputable def tensorLeftEquivalence {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    C ≌ C :=
  .mk (tensorLeft X) (tensorLeft Y)
    ((leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso e'.symm ≪≫ tensorLeftTensor Y X)
    ((tensorLeftTensor X Y).symm ≪≫ (tensoringLeft C).mapIso e ≪≫ leftUnitorNatIso C)

/-- Tensoring on the right with an object `X` with a two-sided tensor inverse `Y` is an
equivalence, with inverse the tensor product with `Y`. -/
@[simps! functor inverse]
noncomputable def tensorRightEquivalence {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    C ≌ C :=
  .mk (tensorRight X) (tensorRight Y)
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e.symm ≪≫ tensorRightTensor X Y)
    ((tensorRightTensor Y X).symm ≪≫ (tensoringRight C).mapIso e' ≪≫ rightUnitorNatIso C)

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

end MonoidalClosed

end CategoryTheory
