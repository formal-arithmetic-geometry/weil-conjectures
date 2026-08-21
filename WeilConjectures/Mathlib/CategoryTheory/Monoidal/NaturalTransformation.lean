/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
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

We also prove the uniqueness half of doctrinal adjunction: if two monoidal functors are
left adjoint to the same lax monoidal functor via monoidal adjunctions, then the canonical
isomorphism between them is a monoidal natural isomorphism
(`CategoryTheory.Adjunction.isMonoidal_leftAdjointUniq_hom`).

Dually, the conjugate of a transformation between the left adjoints that is compatible with
their oplax monoidal structures is a monoidal natural transformation
(`CategoryTheory.isMonoidal_conjugateEquiv`); consequently, if two lax monoidal functors are
right adjoint to the same oplax monoidal functor via monoidal adjunctions, then the canonical
isomorphism between them is a monoidal natural isomorphism
(`CategoryTheory.Adjunction.isMonoidal_rightAdjointUniq_hom`).
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

/-- Dual monoidal mates: if a natural transformation `τ : L₂ ⟶ L₁` between the left adjoints
of two monoidal adjunctions is compatible with the oplax monoidal structure maps of the left
adjoints, then its conjugate `conjugateEquiv adj₁ adj₂ τ : R₁ ⟶ R₂` is a monoidal natural
transformation. The compatibility hypotheses are exactly the two equations produced by
`conjugateEquiv_symm_app_unit_comp_η` and `conjugateEquiv_symm_app_tensor_comp_δ`; they are
spelled out since Mathlib has no notion of monoidal transformation between oplax monoidal
functors. -/
lemma isMonoidal_conjugateEquiv (τ : L₂ ⟶ L₁) (hη : τ.app (𝟙_ C) ≫ η L₁ = η L₂)
    (hδ : ∀ X Y, τ.app (X ⊗ Y) ≫ δ L₁ X Y = δ L₂ X Y ≫ (τ.app X ⊗ₘ τ.app Y)) :
    NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ τ) where
  unit := by
    apply (adj₂.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, τ.naturality_assoc, map_ε_comp_counit_app_unit, hη,
      map_ε_comp_counit_app_unit]
  tensor X Y := by
    apply (adj₂.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, conjugateEquiv_counit, τ.naturality_assoc,
      map_μ_comp_counit_app_tensor, ← Category.assoc, hδ, Category.assoc,
      tensorHom_comp_tensorHom, map_μ_comp_counit_app_tensor, ← δ_natural_assoc,
      tensorHom_comp_tensorHom, conjugateEquiv_counit adj₁ adj₂ τ X,
      conjugateEquiv_counit adj₁ adj₂ τ Y]

/-! ### Uniqueness of monoidal left adjoints -/

namespace Adjunction

variable {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- `Adjunction.leftAdjointUniq` is (definitionally) the inverse conjugate of the identity
natural transformation. -/
lemma leftAdjointUniq_hom_eq_conjugateEquiv_symm_id :
    (adj1.leftAdjointUniq adj2).hom = (conjugateEquiv adj2 adj1).symm (𝟙 G) :=
  rfl

variable [F.Monoidal] [F'.Monoidal] [G.LaxMonoidal] [adj1.IsMonoidal] [adj2.IsMonoidal]

/-- Uniqueness of monoidal left adjoints: if two monoidal functors `F` and `F'` are left
adjoint to the same lax monoidal functor `G` via monoidal adjunctions, then the canonical
isomorphism `adj1.leftAdjointUniq adj2 : F ≅ F'` is a monoidal natural isomorphism. -/
instance isMonoidal_leftAdjointUniq_hom :
    NatTrans.IsMonoidal (adj1.leftAdjointUniq adj2).hom where
  unit := by
    rw [← cancel_mono (η F'), Category.assoc, leftAdjointUniq_hom_eq_conjugateEquiv_symm_id,
      conjugateEquiv_symm_app_unit_comp_η, Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  tensor X Y := by
    rw [← cancel_mono (δ F' X Y), Category.assoc, Category.assoc,
      leftAdjointUniq_hom_eq_conjugateEquiv_symm_id, conjugateEquiv_symm_app_tensor_comp_δ,
      Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

/-- The inverse of the canonical isomorphism between two monoidal left adjoints is monoidal
as well, by the general instance for inverses of monoidal natural isomorphisms. -/
example : NatTrans.IsMonoidal (adj1.leftAdjointUniq adj2).inv := inferInstance

end Adjunction

/-! ### Uniqueness of lax monoidal right adjoints -/

namespace Adjunction

section RightAdjointUniq

variable {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G')

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- `Adjunction.rightAdjointUniq` is (definitionally) the conjugate of the identity
natural transformation. -/
lemma rightAdjointUniq_hom_eq_conjugateEquiv_id :
    (adj1.rightAdjointUniq adj2).hom = conjugateEquiv adj1 adj2 (𝟙 F) :=
  rfl

variable [F.OplaxMonoidal] [G.LaxMonoidal] [G'.LaxMonoidal] [adj1.IsMonoidal]
  [adj2.IsMonoidal]

/-- Uniqueness of lax monoidal right adjoints: if two lax monoidal functors `G` and `G'` are
right adjoint to the same oplax monoidal functor `F` via monoidal adjunctions, then the
canonical isomorphism `adj1.rightAdjointUniq adj2 : G ≅ G'` is a monoidal natural
isomorphism. -/
instance isMonoidal_rightAdjointUniq_hom :
    NatTrans.IsMonoidal (adj1.rightAdjointUniq adj2).hom := by
  rw [rightAdjointUniq_hom_eq_conjugateEquiv_id]
  exact isMonoidal_conjugateEquiv adj1 adj2 (𝟙 F) (by simp) (fun X Y ↦ by simp)

/-- The inverse of the canonical isomorphism between two lax monoidal right adjoints is
monoidal as well, by the general instance for inverses of monoidal natural isomorphisms. -/
example : NatTrans.IsMonoidal (adj1.rightAdjointUniq adj2).inv := inferInstance

end RightAdjointUniq

end Adjunction

end CategoryTheory
