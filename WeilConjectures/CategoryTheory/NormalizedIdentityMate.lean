/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates
/-! Identity normalization of the mates correspondence.
(blueprint: new-lem-pur-ringed-refinement-normalized-identity-mate). -/
@[expose] public section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂ v₃
namespace CategoryTheory
private theorem identityCounitNormalized {C : Type u₁} [Category.{v₁} C]
    {F G : C ⥤ C} (a : F ⊣ G) (f : F ≅ 𝟭 C)
    (g : G ≅ 𝟭 C)
    (h : g.inv = conjugateEquiv Adjunction.id a f.hom) (M : C) :
    F.map (g.inv.app M) ≫ a.counit.app M = f.hom.app M := by
  rw [h]
  simp only [conjugateEquiv_counit]
  change f.hom.app M ≫ 𝟙 M = f.hom.app M
  exact Category.comp_id _

set_option backward.defeqAttrib.useBackward false in
/-- Taking the mate commutes with normalization by an identity adjunction.
Source: coefficient supplement Step 10; Mathlib's mateEquiv_counit and
conjugateEquiv_counit in CategoryTheory.Adjunction.Mates.
Proof: conjugation identifies the identity counit composite with g. Apply the
inverse proper-adjunction Hom equivalence to both sides, expand its counit formula,
and use mateEquiv_counit. Naturality of alpha and functoriality then identify the
composite with alpha followed by the image of g.
(blueprint: new-lem-pur-ringed-refinement-normalized-identity-mate). -/
theorem mateEquiv_identity_refinement
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    {F G : C ⥤ C} {L : D ⥤ E} {R : E ⥤ D}
    (a : L ⊣ R) (i : F ⊣ G) (J₂ : C ⥤ D) (J₁ : C ⥤ E)
    (α : J₂ ⋙ L ⟶ F ⋙ J₁) (g : F ≅ 𝟭 C) (r : G ≅ 𝟭 C)
    (h : r.inv = conjugateEquiv Adjunction.id i g.hom) (M : C) :
    a.homEquiv (J₂.obj M) (J₁.obj M)
      (α.app M ≫ J₁.map (g.hom.app M : F.obj M ⟶ M)) =
      J₂.map (r.inv.app M) ≫ (mateEquiv (G := J₂) (H := J₁) i a α).app M := by
  let δ := r.inv.app M
  have hc : F.map δ ≫ i.counit.app M = g.hom.app M :=
    identityCounitNormalized i g r h M
  apply (a.homEquiv (J₂.obj M) (J₁.obj M)).symm.injective
  rw [Equiv.symm_apply_apply, a.homEquiv_counit]
  change _ = L.map (J₂.map δ ≫ (mateEquiv (G := J₂) (H := J₁) i a α).app M) ≫ a.counit.app _
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    CategoryTheory.mateEquiv_counit i a (TwoSquare.mk J₂ F L J₁ α) M]
  have hn := α.naturality δ
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp, hc]
  rfl

end CategoryTheory
