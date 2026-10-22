/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The symmetric monoidal structure on raw scalar localization

Source: the pure-tensor construction in step 2 of
`lem-sf-tensor-comparison-localization-descent` (blueprint:
lem-sf-scalar-localization-monoidal).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

universe r u v

open TensorProduct CategoryTheory.MonoidalCategory

namespace CategoryTheory.ScalarLocalization

variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (p : R)
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]

/-- Extend left whiskering by its scalar-linear Hom map. -/
def tensorLeftMap (X : C) {Y Z : C}
    (f : Localization.Away p ⊗[R] (Y ⟶ Z)) :
    Localization.Away p ⊗[R] (X ⊗ Y ⟶ X ⊗ Z) :=
  ((tensorLeft X).mapLinearMap R).baseChange (Localization.Away p) f

/-- Extend right whiskering by its scalar-linear Hom map. -/
def tensorRightMap {X Y : C}
    (f : Localization.Away p ⊗[R] (X ⟶ Y)) (Z : C) :
    Localization.Away p ⊗[R] (X ⊗ Z ⟶ Y ⊗ Z) :=
  ((tensorRight Z).mapLinearMap R).baseChange (Localization.Away p) f

@[simp] theorem tensorLeftMap_tmul (X : C) {Y Z : C}
    (a : Localization.Away p) (f : Y ⟶ Z) :
    tensorLeftMap R C p X (a ⊗ₜ[R] f) = a ⊗ₜ[R] (X ◁ f) := by
  simp only [tensorLeftMap, LinearMap.baseChange_tmul]
  rfl

@[simp] theorem tensorRightMap_tmul {X Y : C}
    (a : Localization.Away p) (f : X ⟶ Y) (Z : C) :
    tensorRightMap R C p (a ⊗ₜ[R] f) Z = a ⊗ₜ[R] (f ▷ Z) := by
  simp only [tensorRightMap, LinearMap.baseChange_tmul]
  rfl

/-- The bilinear extension of tensor on morphisms. -/
def tensorMap {X X' Y Y' : C}
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    Localization.Away p ⊗[R] (X ⊗ Y ⟶ X' ⊗ Y') :=
  composition R C p _ _ _ (tensorLeftMap R C p X' g) (tensorRightMap R C p f Y)

@[simp] theorem tensorMap_tmul {X X' Y Y' : C}
    (a b : Localization.Away p) (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorMap R C p (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (f ⊗ₘ g) := by
  simp [tensorMap, composition_tmul, tensorHom_def, mul_comm]

@[simp] theorem tensorMap_zero_left {X X' Y Y' : C}
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    tensorMap R C p (0 : Localization.Away p ⊗[R] (X ⟶ X')) g = 0 := by
  simp only [tensorMap, tensorRightMap, map_zero, map_add, LinearMap.add_apply,
    LinearMap.zero_apply]

@[simp] theorem tensorMap_zero_right {X X' Y Y' : C}
    (f : Localization.Away p ⊗[R] (X ⟶ X')) :
    tensorMap R C p f (0 : Localization.Away p ⊗[R] (Y ⟶ Y')) = 0 := by
  simp only [tensorMap, tensorLeftMap, map_zero, map_add, LinearMap.add_apply,
    LinearMap.zero_apply]

@[simp] theorem tensorMap_add_left {X X' Y Y' : C}
    (f f' : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    tensorMap R C p (f + f') g = tensorMap R C p f g + tensorMap R C p f' g := by
  simp only [tensorMap, tensorRightMap, map_zero, map_add, LinearMap.add_apply,
    LinearMap.zero_apply]

@[simp] theorem tensorMap_add_right {X X' Y Y' : C}
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g g' : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    tensorMap R C p f (g + g') = tensorMap R C p f g + tensorMap R C p f g' := by
  simp only [tensorMap, tensorLeftMap, map_zero, map_add, LinearMap.add_apply,
    LinearMap.zero_apply]

/-- Objects and constraints are unchanged; whiskering extends linearly. -/
@[instance_reducible] def monoidalStruct : MonoidalCategoryStruct (ScalarLocalization R C p) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ f := tensorMap R C p (1 ⊗ₜ[R] 𝟙 X.obj) f
  whiskerRight f Z := tensorMap R C p f (1 ⊗ₜ[R] 𝟙 Z.obj)
  tensorHom f g := tensorMap R C p f g
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := (localization R C p).mapIso (α_ X.obj Y.obj Z.obj)
  leftUnitor X := (localization R C p).mapIso (λ_ X.obj)
  rightUnitor X := (localization R C p).mapIso (ρ_ X.obj)

/-- The extended whiskerings satisfy the monoidal axioms on arbitrary fractions. -/
@[instance_reducible] def monoidal : MonoidalCategory (ScalarLocalization R C p) := by
  letI := monoidalStruct R C p
  refine MonoidalCategory.ofTensorHom ?_ (by intros; rfl) (by intros; rfl)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro X Y
    change tensorMap R C p (1 ⊗ₜ[R] 𝟙 X.obj) (1 ⊗ₜ[R] 𝟙 Y.obj) = _
    simp only [tensorMap_tmul, one_mul, id_tensorHom_id]
    rfl
  · intro X X' X'' Y Y' Y'' f g h k
    change composition R C p _ _ _ (tensorMap R C p h k) (tensorMap R C p f g) =
      tensorMap R C p (composition R C p _ _ _ h f) (composition R C p _ _ _ k g)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f f' hf hf' => simp [hf, hf']
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp
      | add g g' hg hg' => simp [hg, hg']
      | tmul b g =>
        induction h using TensorProduct.induction_on with
        | zero => simp
        | add h h' hh hh' => simp only [tensorMap_add_left, tensorMap_add_right, map_add,
          LinearMap.add_apply, hh, hh']
        | tmul c h =>
          induction k using TensorProduct.induction_on with
          | zero => simp
          | add k k' hk hk' => simp only [tensorMap_add_left, tensorMap_add_right, map_add,
            LinearMap.add_apply, hk, hk']
          | tmul d k =>
            simp only [tensorMap_tmul, composition_tmul, tensorHom_comp_tensorHom]
            congr 1
            ring
  · intro X Y Z X' Y' Z' f g h
    change composition R C p _ _ _ (1 ⊗ₜ[R] (α_ X'.obj Y'.obj Z'.obj).hom)
        (tensorMap R C p (tensorMap R C p f g) h) =
      composition R C p _ _ _ (tensorMap R C p f (tensorMap R C p g h))
        (1 ⊗ₜ[R] (α_ X.obj Y.obj Z.obj).hom)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f f' hf hf' => simp [hf, hf']
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero => simp
      | add g g' hg hg' => simp [hg, hg']
      | tmul b g =>
        induction h using TensorProduct.induction_on with
        | zero => simp
        | add h h' hh hh' => simp only [tensorMap_add_left, tensorMap_add_right, map_add,
          LinearMap.add_apply, hh, hh']
        | tmul c h =>
          simp only [tensorMap_tmul, composition_tmul, mul_one, one_mul, mul_assoc,
            associator_naturality]
  · intro X Y f
    change composition R C p _ _ _ (1 ⊗ₜ[R] (λ_ Y.obj).hom)
      (tensorMap R C p (1 ⊗ₜ[R] 𝟙 (𝟙_ C)) f) =
      composition R C p _ _ _ f (1 ⊗ₜ[R] (λ_ X.obj).hom)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg => simp [hf, hg]
    | tmul a f =>
      simp only [tensorMap_tmul, composition_tmul, mul_one, one_mul,
        id_tensorHom, leftUnitor_naturality]
  · intro X Y f
    change composition R C p _ _ _ (1 ⊗ₜ[R] (ρ_ Y.obj).hom)
      (tensorMap R C p f (1 ⊗ₜ[R] 𝟙 (𝟙_ C))) =
      composition R C p _ _ _ f (1 ⊗ₜ[R] (ρ_ X.obj).hom)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg => simp [hf, hg]
    | tmul a f =>
      simp only [tensorMap_tmul, composition_tmul, mul_one, one_mul,
        tensorHom_id, rightUnitor_naturality]
  · intro W X Y Z
    change composition R C p _ _ _
      (composition R C p _ _ _
        (tensorMap R C p (1 ⊗ₜ[R] 𝟙 W.obj) (1 ⊗ₜ[R] (α_ X.obj Y.obj Z.obj).hom))
        (1 ⊗ₜ[R] (α_ W.obj (X.obj ⊗ Y.obj) Z.obj).hom))
      (tensorMap R C p (1 ⊗ₜ[R] (α_ W.obj X.obj Y.obj).hom) (1 ⊗ₜ[R] 𝟙 Z.obj)) =
      composition R C p _ _ _ (1 ⊗ₜ[R] (α_ W.obj X.obj (Y.obj ⊗ Z.obj)).hom)
        (1 ⊗ₜ[R] (α_ (W.obj ⊗ X.obj) Y.obj Z.obj).hom)
    simp only [tensorMap_tmul, composition_tmul, one_mul, tensorHom_id, id_tensorHom,
      Category.assoc, pentagon]
  · intro X Y
    change composition R C p _ _ _
      (tensorMap R C p (1 ⊗ₜ[R] 𝟙 X.obj) (1 ⊗ₜ[R] (λ_ Y.obj).hom))
        (1 ⊗ₜ[R] (α_ X.obj (𝟙_ C) Y.obj).hom) =
      tensorMap R C p (1 ⊗ₜ[R] (ρ_ X.obj).hom) (1 ⊗ₜ[R] 𝟙 Y.obj)
    simp only [tensorMap_tmul, composition_tmul, one_mul, tensorHom_id, id_tensorHom,
      triangle]

attribute [local instance] monoidal

/-- The localized tensor is additive in each variable. -/
theorem monoidalPreadditive : MonoidalPreadditive (ScalarLocalization R C p) where
  whiskerLeft_zero := by intros; exact tensorMap_zero_right R C p _
  zero_whiskerRight := by intros; exact tensorMap_zero_left R C p _
  whiskerLeft_add := by intros; exact tensorMap_add_right R C p _ _ _
  add_whiskerRight := by intros; exact tensorMap_add_left R C p _ _ _

attribute [local instance] monoidalPreadditive

/-- The localized tensor is linear over the localized coefficient ring. -/
theorem monoidalLinear : MonoidalLinear (Localization.Away p) (ScalarLocalization R C p) where
  whiskerLeft_smul := by
    intro X Y Z a f
    change tensorMap R C p _ (a • f) = a • tensorMap R C p _ f
    simp only [tensorMap, tensorLeftMap, map_smul, LinearMap.smul_apply]
  smul_whiskerRight := by
    intro a X Y f Z
    change tensorMap R C p (a • f) _ = a • tensorMap R C p f _
    simp only [tensorMap, tensorRightMap, map_smul]

variable [SymmetricCategory C]

/-- The original symmetry, tensored with one, satisfies the hexagon equations. -/
@[instance_reducible] def symmetric : SymmetricCategory (ScalarLocalization R C p) where
  braiding X Y := (localization R C p).mapIso (β_ X.obj Y.obj)
  braiding_naturality_right := by
    intro X Y Z f
    change composition R C p _ _ _ (1 ⊗ₜ[R] (β_ X.obj Z.obj).hom)
        (tensorMap R C p (1 ⊗ₜ[R] 𝟙 X.obj) f) =
      composition R C p _ _ _ (tensorMap R C p f (1 ⊗ₜ[R] 𝟙 X.obj))
        (1 ⊗ₜ[R] (β_ X.obj Y.obj).hom)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg => simp only [tensorMap_add_left, tensorMap_add_right, map_add,
        LinearMap.add_apply, hf, hg]
    | tmul a f =>
      simp only [tensorMap_tmul, composition_tmul, one_mul, mul_one, id_tensorHom,
        tensorHom_id, BraidedCategory.braiding_naturality_right]
  braiding_naturality_left := by
    intro X Y f Z
    change composition R C p _ _ _ (1 ⊗ₜ[R] (β_ Y.obj Z.obj).hom)
        (tensorMap R C p f (1 ⊗ₜ[R] 𝟙 Z.obj)) =
      composition R C p _ _ _ (tensorMap R C p (1 ⊗ₜ[R] 𝟙 Z.obj) f)
        (1 ⊗ₜ[R] (β_ X.obj Z.obj).hom)
    induction f using TensorProduct.induction_on with
    | zero => simp
    | add f g hf hg => simp only [tensorMap_add_left, tensorMap_add_right, map_add,
        LinearMap.add_apply, hf, hg]
    | tmul a f =>
      simp only [tensorMap_tmul, composition_tmul, one_mul, mul_one, id_tensorHom,
        tensorHom_id, BraidedCategory.braiding_naturality_left]
  hexagon_forward X Y Z := by
    change composition R C p _ _ _
      (composition R C p _ _ _ (1 ⊗ₜ[R] (α_ Y.obj Z.obj X.obj).hom)
        (1 ⊗ₜ[R] (β_ X.obj (Y.obj ⊗ Z.obj)).hom))
      (1 ⊗ₜ[R] (α_ X.obj Y.obj Z.obj).hom) =
      composition R C p _ _ _
        (composition R C p _ _ _
          (tensorMap R C p (1 ⊗ₜ[R] 𝟙 Y.obj) (1 ⊗ₜ[R] (β_ X.obj Z.obj).hom))
          (1 ⊗ₜ[R] (α_ Y.obj X.obj Z.obj).hom))
        (tensorMap R C p (1 ⊗ₜ[R] (β_ X.obj Y.obj).hom) (1 ⊗ₜ[R] 𝟙 Z.obj))
    simp only [tensorMap_tmul, composition_tmul, one_mul, id_tensorHom, tensorHom_id,
      BraidedCategory.hexagon_forward]
  hexagon_reverse X Y Z := by
    change composition R C p _ _ _
      (composition R C p _ _ _ (1 ⊗ₜ[R] (α_ Z.obj X.obj Y.obj).inv)
        (1 ⊗ₜ[R] (β_ (X.obj ⊗ Y.obj) Z.obj).hom))
      (1 ⊗ₜ[R] (α_ X.obj Y.obj Z.obj).inv) =
      composition R C p _ _ _
        (composition R C p _ _ _
          (tensorMap R C p (1 ⊗ₜ[R] (β_ X.obj Z.obj).hom) (1 ⊗ₜ[R] 𝟙 Y.obj))
          (1 ⊗ₜ[R] (α_ X.obj Z.obj Y.obj).inv))
        (tensorMap R C p (1 ⊗ₜ[R] 𝟙 X.obj) (1 ⊗ₜ[R] (β_ Y.obj Z.obj).hom))
    simp only [tensorMap_tmul, composition_tmul, one_mul, id_tensorHom, tensorHom_id,
      BraidedCategory.hexagon_reverse]
  symmetry X Y := by
    change composition R C p _ _ _ (1 ⊗ₜ[R] (β_ Y.obj X.obj).hom)
      (1 ⊗ₜ[R] (β_ X.obj Y.obj).hom) = _
    simp only [composition_tmul, one_mul, SymmetricCategory.symmetry]
    rfl

end CategoryTheory.ScalarLocalization
