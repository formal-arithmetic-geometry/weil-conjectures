/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Abstract

/-!

# Composition and transport of projection morphisms

For adjunctions `F ⊣ G` with `F` oplax monoidal (the pullback–pushforward adjunctions of proper
morphisms) and `P ⊣ S` with `S` lax monoidal (the extension by zero along open immersions), the
projection morphism and the projection comparison of a composite adjunction are the composites of
those of the factors (`CategoryTheory.Adjunction.projectionMorphism_comp`,
`CategoryTheory.Adjunction.projectionComparison_comp`), and the projection morphism is transported
along an isomorphism of left adjoints compatible with the comultiplications
(`CategoryTheory.Adjunction.projectionMorphism_eq_of_iso`). These are the formal parts of the
composition clause of the coherence of the projection formula (blueprint `prop-sf-pf-coherence`).

-/

@[expose] public section
open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃]
  {F₁ : C₂ ⥤ C₁} {G₁ : C₁ ⥤ C₂} {F₂ : C₃ ⥤ C₂} {G₂ : C₂ ⥤ C₃}
  [F₁.OplaxMonoidal] [F₂.OplaxMonoidal] (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂)

/-- The projection morphism of a composite adjunction is the composite of the projection
morphisms. -/
lemma projectionMorphism_comp (A : C₁) (B : C₃) :
    (a₂.comp a₁).projectionMorphism A B =
      a₂.projectionMorphism (G₁.obj A) B ≫ G₂.map (a₁.projectionMorphism A (F₂.obj B)) := by
  rw [projectionMorphism, projectionMorphism, projectionMorphism, comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [← homEquiv_naturality_right, ← homEquiv_naturality_left]
  simp [Functor.OplaxMonoidal.comp_δ, comp_counit_app, δ_natural_left_assoc]

section Comparison

variable {P₁ : C₁ ⥤ C₂} {S₁ : C₂ ⥤ C₁} {P₂ : C₂ ⥤ C₃} {S₂ : C₃ ⥤ C₂}
  [S₁.LaxMonoidal] [S₂.LaxMonoidal] (b₁ : P₁ ⊣ S₁) (b₂ : P₂ ⊣ S₂)

open Functor.LaxMonoidal in
/-- The projection comparison of a composite adjunction is the composite of the projection
comparisons. -/
lemma projectionComparison_comp (M : C₁) (N : C₃) :
    (b₁.comp b₂).projectionComparison M N =
      P₂.map (b₁.projectionComparison M (S₂.obj N)) ≫ b₂.projectionComparison (P₁.obj M) N := by
  rw [projectionComparison, projectionComparison, projectionComparison, comp_homEquiv]
  dsimp only [Equiv.symm_trans_apply]
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm]
  congr 1
  simp [Functor.LaxMonoidal.comp_μ, comp_unit_app]

end Comparison

section Transport

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] [MonoidalCategory D₁] [MonoidalCategory D₂]
  {F F' : D₂ ⥤ D₁} {G G' : D₁ ⥤ D₂} [F.OplaxMonoidal] [F'.OplaxMonoidal]
  (a : F ⊣ G) (a' : F' ⊣ G') (e : F ≅ F')

/-- The projection morphism is transported along an isomorphism `e : F ≅ F'` of oplax monoidal
left adjoints compatible with the comultiplications, through the conjugate `G' ≅ G`. -/
lemma projectionMorphism_eq_of_iso
    (he : ∀ X Y, δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y) = e.hom.app (X ⊗ Y) ≫ δ F' X Y)
    (A : D₁) (B : D₂) :
    a.projectionMorphism A B =
      (conjugateIsoEquiv a' a e).inv.app A ▷ B ≫ a'.projectionMorphism A B ≫
        (conjugateIsoEquiv a' a e).hom.app _ ≫ G.map (A ◁ e.inv.app B) := by
  have h1 : ∀ Z, F.map ((conjugateIsoEquiv a' a e).hom.app Z) ≫ a.counit.app Z =
      e.hom.app (G'.obj Z) ≫ a'.counit.app Z := fun Z ↦ conjugateEquiv_counit a' a e.hom Z
  have h2 : e.hom.app (G.obj A) ≫ F'.map ((conjugateIsoEquiv a' a e).inv.app A) ≫
      a'.counit.app A = a.counit.app A := by
    rw [show (conjugateIsoEquiv a' a e).inv = conjugateEquiv a a' e.inv from rfl,
      conjugateEquiv_counit, Iso.hom_inv_id_app_assoc]
  have h3 : F'.map (a'.projectionMorphism A B) ≫ a'.counit.app _ =
      δ F' (G'.obj A) B ≫ a'.counit.app A ▷ F'.obj B := by
    refine (a'.homEquiv_counit (g := a'.projectionMorphism A B)).symm.trans ?_
    rw [projectionMorphism, Equiv.symm_apply_apply]
  apply (a.homEquiv _ _).symm.injective
  rw [projectionMorphism, Equiv.symm_apply_apply, homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality]
  rw [reassoc_of% (h1 (A ⊗ F'.obj B))]
  rw [e.hom.naturality_assoc, e.hom.naturality_assoc, reassoc_of% h3,
    ← δ_natural_left_assoc, ← reassoc_of% (he (G.obj A) B)]
  rw [← h2]
  simp only [tensorHom_def, Category.assoc, comp_whiskerRight, whisker_exchange_assoc,
    ← whiskerLeft_comp, Iso.hom_inv_id_app, whiskerLeft_id, Category.comp_id]

end Transport

end CategoryTheory.Adjunction
