/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalTensorComparisonSystem
public import Sheaf.CategoryTheory.ScalarLocalizationMonoidal

/-! # Explicit normalized rational tensor structures

Source: step 2 of the conditional tensor-comparison construction, blueprint order 1826
(blueprint: lem-sf-rational-comparison-structures).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures.TensorComparisonDescent

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]

/-- The symmetric monoidal structures are the explicit scalar-linear extensions.
Source: blueprint order 1826, conditional argument step 2
(blueprint: lem-sf-rational-comparison-structures). -/
@[instance_reducible] def rationalStructures : RationalStructures C where
  monoidal E := ScalarLocalization.monoidal (Integers l Ω E) (C E) (uniformizer l Ω E)
  symmetric E := ScalarLocalization.symmetric (Integers l Ω E) (C E) (uniformizer l Ω E)

attribute [local instance] rationalStructures

/-- Tensor objects remain the original tensor objects. -/
theorem rationalStructures_tensorObject (E : Index l Ω) (X Y : Rat C E) :
    X ⊗ Y = ⟨X.obj ⊗ Y.obj⟩ := rfl

/-- The unit object remains the original unit. -/
theorem rationalStructures_unitObject (E : Index l Ω) :
    (𝟙_ (Rat C E)) = ⟨𝟙_ (C E)⟩ := rfl

/-- Tensoring pure morphisms multiplies exactly their scalar coefficients. -/
theorem rationalStructures_tensorArrow (E : Index l Ω) (X X' Y Y' : Rat C E)
    (f : X.obj ⟶ X'.obj) (g : Y.obj ⟶ Y'.obj)
    (a b : Localization.Away (uniformizer l Ω E)) :
    HEq (@MonoidalCategoryStruct.tensorHom (Rat C E) _ _ X X' Y Y'
      (a ⊗ₜ[Integers l Ω E] f) (b ⊗ₜ[Integers l Ω E] g))
      ((a * b) ⊗ₜ[Integers l Ω E] (f ⊗ₘ g) :
        (⟨X.obj ⊗ Y.obj⟩ : Rat C E) ⟶ ⟨X'.obj ⊗ Y'.obj⟩) := by
  exact heq_of_eq (ScalarLocalization.tensorMap_tmul _ _ _ a b f g)

/-- The associator is the original associator tensored with one. -/
theorem rationalStructures_associator (E : Index l Ω) (X Y Z : Rat C E) :
    HEq (α_ X Y Z).hom ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (α_ X.obj Y.obj Z.obj).hom) := HEq.rfl

/-- The braiding retains the original signed symmetry. -/
theorem rationalStructures_symmetry (E : Index l Ω) (X Y : Rat C E) :
    HEq (β_ X Y).hom ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (β_ X.obj Y.obj).hom) := HEq.rfl

/-- The left unitor is tensored with one. -/
theorem rationalStructures_leftUnitor (E : Index l Ω) (X : Rat C E) :
    HEq (λ_ X).hom ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (λ_ X.obj).hom) := HEq.rfl

/-- The right unitor is tensored with one. -/
theorem rationalStructures_rightUnitor (E : Index l Ω) (X : Rat C E) :
    HEq (ρ_ X).hom ((1 : Localization.Away (uniformizer l Ω E)) ⊗ₜ[
      Integers l Ω E] (ρ_ X.obj).hom) := HEq.rfl

/-- The extended tensor is bilinear over the localized coefficient ring. -/
theorem rationalStructures_bilinear (E : Index l Ω) :
    ∃ h : MonoidalPreadditive (Rat C E),
      letI := h
      MonoidalLinear (Localization.Away (uniformizer l Ω E)) (Rat C E) := by
  refine ⟨ScalarLocalization.monoidalPreadditive _ _ _, ?_⟩
  exact ScalarLocalization.monoidalLinear _ _ _

end WeilConjectures.TensorComparisonDescent
