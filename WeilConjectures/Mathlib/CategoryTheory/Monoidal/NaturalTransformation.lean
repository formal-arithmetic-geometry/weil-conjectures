/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal mates: conjugates of monoidal transformations are compatible with
# the oplax structures on the left adjoints

Let `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions between monoidal categories,
where the left adjoints are oplax monoidal, the right adjoints are lax monoidal, and both
adjunctions are monoidal (`Adjunction.IsMonoidal`). We show that for a monoidal natural
transformation `e : R₁ ⟶ R₂`, the conjugate transformation
`(conjugateEquiv adj₁ adj₂).symm e : L₂ ⟶ L₁` is compatible with the oplax monoidal
structure maps of the left adjoints:

- `CategoryTheory.conjugateEquiv_symm_app_unit_comp_η`: compatibility with the unit
  comparisons `η`.
- `CategoryTheory.conjugateEquiv_symm_app_tensor_comp_δ`: compatibility with the tensor
  comparisons `δ`.

As a consequence, isomorphy of the oplax structure maps transfers across a conjugate
isomorphism (`CategoryTheory.isIso_η_of_conjugateIso` and
`CategoryTheory.isIso_δ_of_conjugateIso`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Adjunction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- The conjugate of a monoidal natural transformation between the right adjoints of two
monoidal adjunctions is compatible with the unit comparisons `η` of the oplax monoidal
structures on the left adjoints. -/
@[reassoc]
lemma conjugateEquiv_symm_app_unit_comp_η (e : R₁ ⟶ R₂) [NatTrans.IsMonoidal e] :
    ((conjugateEquiv adj₁ adj₂).symm e).app (𝟙_ C) ≫ η L₁ = η L₂ := by
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← e.naturality,
    unit_app_unit_comp_map_η_assoc, NatTrans.IsMonoidal.unit,
    unit_app_unit_comp_map_η]

/-- The conjugate of a monoidal natural transformation between the right adjoints of two
monoidal adjunctions is compatible with the tensor comparisons `δ` of the oplax monoidal
structures on the left adjoints. -/
@[reassoc]
lemma conjugateEquiv_symm_app_tensor_comp_δ (e : R₁ ⟶ R₂) [NatTrans.IsMonoidal e]
    (X Y : C) :
    ((conjugateEquiv adj₁ adj₂).symm e).app (X ⊗ Y) ≫ δ L₁ X Y =
      δ L₂ X Y ≫ (((conjugateEquiv adj₁ adj₂).symm e).app X ⊗ₘ
        ((conjugateEquiv adj₁ adj₂).symm e).app Y) := by
  apply (adj₂.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← e.naturality,
    unit_app_tensor_comp_map_δ_assoc, NatTrans.IsMonoidal.tensor,
    tensorHom_comp_tensorHom_assoc, unit_conjugateEquiv_symm adj₁ adj₂ e X,
    unit_conjugateEquiv_symm adj₁ adj₂ e Y, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural, unit_app_tensor_comp_map_δ_assoc]

include adj₁ adj₂ in
/-- If the right adjoints of two monoidal adjunctions are isomorphic via a monoidal
natural isomorphism and the unit comparison `η` of one left adjoint is an isomorphism,
then so is the other: isomorphy of `η` transfers across a conjugate isomorphism. -/
lemma isIso_η_of_conjugateIso (e : R₁ ≅ R₂) [NatTrans.IsMonoidal e.hom] [IsIso (η L₂)] :
    IsIso (η L₁) := by
  have : IsIso (((conjugateEquiv adj₁ adj₂).symm e.hom).app (𝟙_ C) ≫ η L₁) := by
    rw [conjugateEquiv_symm_app_unit_comp_η]
    infer_instance
  exact IsIso.of_isIso_comp_left (((conjugateEquiv adj₁ adj₂).symm e.hom).app (𝟙_ C)) _

include adj₁ adj₂ in
/-- If the right adjoints of two monoidal adjunctions are isomorphic via a monoidal
natural isomorphism and the tensor comparison `δ` of one left adjoint is an isomorphism,
then so is the other: isomorphy of `δ` transfers across a conjugate isomorphism. -/
lemma isIso_δ_of_conjugateIso (e : R₁ ≅ R₂) [NatTrans.IsMonoidal e.hom] (X Y : C)
    [IsIso (δ L₂ X Y)] : IsIso (δ L₁ X Y) := by
  have : IsIso (((conjugateEquiv adj₁ adj₂).symm e.hom).app (X ⊗ Y) ≫ δ L₁ X Y) := by
    rw [conjugateEquiv_symm_app_tensor_comp_δ]
    infer_instance
  exact IsIso.of_isIso_comp_left (((conjugateEquiv adj₁ adj₂).symm e.hom).app (X ⊗ Y)) _

end CategoryTheory
