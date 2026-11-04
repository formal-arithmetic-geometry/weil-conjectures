/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!

# Operations on adjunctions with a parameter

Let `adj₂ : F ⊣₂ G` be an adjunction with a parameter, with `F : C₁ ⥤ C₂ ⥤ C₃` and
`G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`. This file constructs new adjunctions with a parameter from `adj₂`, and
shows that the right adjoint bifunctor is unique up to a unique isomorphism compatible with a
given isomorphism of left adjoint bifunctors.

## Main definitions

- `CategoryTheory.ParametrizedAdjunction.precomp`: changing the parameter along a functor
  `P : C₁' ⥤ C₁` gives `P ⋙ F ⊣₂ P.op ⋙ G`.
- `CategoryTheory.ParametrizedAdjunction.comp`: composing with adjunctions `L ⊣ R` (on the
  source `C₂`) and `L' ⊣ R'` (on the target `C₃`) gives `(X₁, X₂) ↦ L' ((F X₁) (L X₂))` left
  adjoint to `(X₁, X₃) ↦ R ((G X₁) (R' X₃))`.
- `CategoryTheory.ParametrizedAdjunction.conjugateIso`: an isomorphism `F' ≅ F` of left
  adjoint bifunctors induces the isomorphism `G ≅ G'` of right adjoint bifunctors which is
  objectwise the conjugate isomorphism (`CategoryTheory.conjugateIsoEquiv`).

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Opposite CategoryTheory.Functor

namespace ParametrizedAdjunction

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj₂ : F ⊣₂ G)

section Precomp

variable {C₁' : Type u₄} [Category.{v₄} C₁'] (P : C₁' ⥤ C₁)

/-- Changing the parameter of an adjunction with a parameter `F ⊣₂ G` along a functor
`P : C₁' ⥤ C₁` gives an adjunction with a parameter `P ⋙ F ⊣₂ P.op ⋙ G`. -/
@[simps]
def precomp : P ⋙ F ⊣₂ P.op ⋙ G where
  adj X₁ := adj₂.adj (P.obj X₁)
  unit_whiskerRight_map f := adj₂.unit_whiskerRight_map (P.map f)

end Precomp

section Comp

variable {C₂' : Type u₅} {C₃' : Type u₆} [Category.{v₅} C₂'] [Category.{v₆} C₃']
  {L : C₂' ⥤ C₂} {R : C₂ ⥤ C₂'} (a : L ⊣ R) {L' : C₃ ⥤ C₃'} {R' : C₃' ⥤ C₃} (b : L' ⊣ R')

/-- Composing an adjunction with a parameter `F ⊣₂ G` with adjunctions `L ⊣ R` on the source
and `L' ⊣ R'` on the target: the bifunctor `(X₁, X₂) ↦ L' ((F X₁) (L X₂))` is left adjoint,
with a parameter, to `(X₁, X₃) ↦ R ((G X₁) (R' X₃))`. -/
@[simps! adj]
def comp :
    F ⋙ (whiskeringLeft _ _ _).obj L ⋙ (whiskeringRight _ _ _).obj L' ⊣₂
      G ⋙ (whiskeringLeft _ _ _).obj R' ⋙ (whiskeringRight _ _ _).obj R :=
  .mk' (fun X₁ ↦ a.comp ((adj₂.adj X₁).comp b)) (fun {X₁ Y₁} f {X₂ X₃} g ↦ by
    dsimp
    simp only [Adjunction.comp_homEquiv]
    erw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply]
    have h := adj₂.homEquiv_naturality_one f (b.homEquiv _ _ g)
    rw [homEquiv_eq, homEquiv_eq] at h
    rw [b.homEquiv_naturality_left, h, a.homEquiv_naturality_right]
    rfl)

end Comp

section ConjugateIso

variable {F' : C₁ ⥤ C₂ ⥤ C₃} {G' : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj₂' : F' ⊣₂ G')

/-- An isomorphism `F' ≅ F` between the left adjoints of two adjunctions with a parameter
`F ⊣₂ G` and `F' ⊣₂ G'` induces an isomorphism `G ≅ G'` of the right adjoints; its component
at `X₁` is the conjugate (`CategoryTheory.conjugateIsoEquiv`) of the component of `e` at
`X₁`. -/
def conjugateIso (e : F' ≅ F) : G ≅ G' :=
  NatIso.ofComponents
    (fun X₁ ↦ conjugateIsoEquiv (adj₂.adj X₁.unop) (adj₂'.adj X₁.unop) (e.app X₁.unop))
    (fun {X₁ Y₁} g ↦ by
      ext X₃
      apply ((adj₂'.adj Y₁.unop).homEquiv _ _).symm.injective
      dsimp
      have h₁ := conjugateEquiv_counit (adj₂.adj Y₁.unop) (adj₂'.adj Y₁.unop)
        (e.hom.app Y₁.unop) X₃
      have h₂ := conjugateEquiv_counit (adj₂.adj X₁.unop) (adj₂'.adj X₁.unop)
        (e.hom.app X₁.unop) X₃
      have h₃ := NatTrans.congr_app (adj₂.whiskerLeft_map_counit g.unop) X₃
      have h₄ := NatTrans.congr_app (adj₂'.whiskerLeft_map_counit g.unop) X₃
      dsimp at h₁ h₂ h₃ h₄
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
        conjugateIsoEquiv_apply_hom, Iso.app_hom]
      rw [h₁, ← h₄, (F'.map g.unop).naturality_assoc, h₂,
        (e.hom.app _).naturality_assoc, ← h₃, ← NatTrans.comp_app_assoc,
        ← NatTrans.comp_app_assoc, e.hom.naturality])

lemma conjugateIso_app (e : F' ≅ F) (X₁ : C₁ᵒᵖ) :
    (adj₂.conjugateIso adj₂' e).app X₁ =
      conjugateIsoEquiv (adj₂.adj X₁.unop) (adj₂'.adj X₁.unop) (e.app X₁.unop) :=
  rfl

/-- The components of `conjugateIso` are characterized by the counits: the transpose of
`((conjugateIso e).app X₁).hom.app X₃` along `F' X₁ ⊣ G' X₁` is `e.hom` followed by the counit
of `F X₁ ⊣ G X₁`. -/
lemma map_conjugateIso_app_hom_app_comp_counit (e : F' ≅ F) (X₁ : C₁ᵒᵖ) (X₃ : C₃) :
    (F'.obj X₁.unop).map (((adj₂.conjugateIso adj₂' e).app X₁).hom.app X₃) ≫
        (adj₂'.adj X₁.unop).counit.app X₃ =
      (e.hom.app X₁.unop).app ((G.obj X₁).obj X₃) ≫ (adj₂.adj X₁.unop).counit.app X₃ :=
  conjugateEquiv_counit (adj₂.adj X₁.unop) (adj₂'.adj X₁.unop) (e.hom.app X₁.unop) X₃

end ConjugateIso

section Equivalence

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C} {T' : D ⥤ D ⥤ D} {H' : Dᵒᵖ ⥤ D ⥤ D}

/-- Transport of the right adjoint along an equivalence: if an equivalence `E : C ≌ D`
intertwines the left adjoints of adjunctions with a parameter `T ⊣₂ H` on `C` and `T' ⊣₂ H'`
on `D`, `E (T P X) ≅ T' (E P) (E X)` naturally in `P` and `X`, then it intertwines the right
adjoints: `E (H P Q) ≅ H' (E P) (E Q)`, naturally in `P` and `Q`. -/
noncomputable def transportIso (adj : T ⊣₂ H) (adj' : T' ⊣₂ H') (E : C ≌ D)
    (τ : T ⋙ (whiskeringRight C C D).obj E.functor ≅
      E.functor ⋙ T' ⋙ (whiskeringLeft C D D).obj E.functor) :
    H ⋙ (whiskeringRight C C D).obj E.functor ≅
      E.functor.op ⋙ H' ⋙ (whiskeringLeft C D D).obj E.functor :=
  (adj.comp E.symm.toAdjunction (Adjunction.id (C := C))).conjugateIso
    ((adj'.precomp E.functor).comp (Adjunction.id (C := D)) E.symm.toAdjunction)
    (NatIso.ofComponents (fun P ↦ NatIso.ofComponents (fun Y ↦
      E.inverse.mapIso ((T'.obj (E.functor.obj P)).mapIso (E.counitIso.app Y).symm ≪≫
        ((τ.app P).app (E.inverse.obj Y)).symm) ≪≫ (E.unitIso.app _).symm) (by
          intro Y Y' f
          have h₁ := (τ.inv.app P).naturality (E.inverse.map f)
          have h₂ := E.unitIso.inv.naturality ((T.obj P).map (E.inverse.map f))
          have h₃ := E.counitIso.inv.naturality f
          dsimp at h₁ h₂ h₃ ⊢
          rw [Category.assoc, ← h₂]
          simp only [← Functor.map_comp_assoc, Category.assoc]
          congr 2
          rw [← h₁, ← Functor.map_comp_assoc, ← h₃, Functor.map_comp_assoc])) (by
      intro P P' g
      ext Y
      have h₁ := NatTrans.congr_app (τ.inv.naturality g) (E.inverse.obj Y)
      have h₂ := E.unitIso.inv.naturality ((T.map g).app (E.inverse.obj Y))
      dsimp at h₁ h₂ ⊢
      rw [Category.assoc, ← h₂]
      simp only [← Functor.map_comp_assoc, Category.assoc]
      congr 2
      rw [← h₁, ← NatTrans.naturality_assoc]))

end Equivalence

end ParametrizedAdjunction

end CategoryTheory
