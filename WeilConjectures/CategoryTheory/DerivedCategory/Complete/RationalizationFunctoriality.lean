/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization

/-!
# Functoriality of the rationalization along torsion-preserving functors

A triangulated functor `F : C ⥤ D` between triangulated categories linear over possibly
different rings `R` and `R'`, which carries `M`-torsion objects to `M'`-torsion objects, induces a
functor `Rationalization M C ⥤ Rationalization M' D`
(`CategoryTheory.Rationalization.mapOfTorsion`). This applies to functors semilinear along a ring
morphism `φ : R →+* R'` with `φ(M) ⊆ M'`
(`CategoryTheory.Rationalization.torsion_obj_of_semilinear`), such as the change of coefficients
`D_comp(X, 𝒪_E) ⥤ D_comp(X, 𝒪_L)` along a finite extension `L/E`.

An isomorphism `F ⋙ G ≅ H` induces an isomorphism of the induced functors
(`CategoryTheory.Rationalization.mapOfTorsionCompIso`), and these isomorphisms inherit the cocycle
condition (`CategoryTheory.Rationalization.mapOfTorsionCompIso_cocycle`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Rationalization

variable {R₁ : Type w₁} [CommRing R₁] (M₁ : Submonoid R₁)
  {C₁ : Type u₁} [Category.{v₁} C₁] [Preadditive C₁] [Linear R₁ C₁] [HasZeroObject C₁]
  [HasShift C₁ ℤ] [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₁ n).Linear R₁]
  [Pretriangulated C₁] [IsTriangulated C₁]
  {R₂ : Type w₂} [CommRing R₂] (M₂ : Submonoid R₂)
  {C₂ : Type u₂} [Category.{v₂} C₂] [Preadditive C₂] [Linear R₂ C₂] [HasZeroObject C₂]
  [HasShift C₂ ℤ] [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Linear R₂]
  [Pretriangulated C₂] [IsTriangulated C₂]

section Map

variable (F : C₁ ⥤ C₂) [F.CommShift ℤ] [F.IsTriangulated]
  (hF : ∀ X, torsion M₁ C₁ X → torsion M₂ C₂ (F.obj X))

include hF in
/-- A triangulated functor carrying `M₁`-torsion objects to `M₂`-torsion objects preserves the
morphisms with torsion mapping cone. -/
lemma W_map_of_torsion {X Y : C₁} {s : X ⟶ Y} (hs : W M₁ C₁ s) : W M₂ C₂ (F.map s) := by
  obtain ⟨Z, g, h, hT, hZ⟩ := hs
  exact ObjectProperty.trW.mk _ (F.map_distinguished _ hT) (hF Z hZ)

/-- The functor `Rationalization M₁ C₁ ⥤ Rationalization M₂ C₂` induced by a triangulated functor
carrying torsion objects to torsion objects. -/
noncomputable def mapOfTorsion : Rationalization M₁ C₁ ⥤ Rationalization M₂ C₂ :=
  Localization.lift (F ⋙ Q M₂ C₂)
    (fun _ _ _ hs ↦ Localization.inverts (Q M₂ C₂) (W M₂ C₂) _ (W_map_of_torsion M₁ M₂ F hF hs))
    (Q M₁ C₁)

noncomputable instance : Localization.Lifting (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₂ C₂)
    (mapOfTorsion M₁ M₂ F hF) :=
  ⟨Localization.fac _ _ _⟩

omit [F.CommShift ℤ] [F.IsTriangulated] in
/-- A functor semilinear along a ring morphism `φ` with `φ(M₁) ⊆ M₂` carries torsion objects to
torsion objects. -/
lemma torsion_obj_of_semilinear [F.PreservesZeroMorphisms] (φ : R₁ →+* R₂) (hM : M₁.map φ ≤ M₂)
    (hF : ∀ (X : C₁) (r : R₁), F.map (r • 𝟙 X) = φ r • 𝟙 (F.obj X)) (X : C₁)
    (hX : torsion M₁ C₁ X) : torsion M₂ C₂ (F.obj X) := by
  obtain ⟨m, hm, h⟩ := hX
  exact ⟨φ m, hM ⟨m, hm, rfl⟩, by rw [← hF, h, F.map_zero]⟩

end Map

section Comp

variable {M₁ M₂} {R₃ : Type w₃} [CommRing R₃] {M₃ : Submonoid R₃}
  {C₃ : Type u₃} [Category.{v₃} C₃] [Preadditive C₃] [Linear R₃ C₃] [HasZeroObject C₃]
  [HasShift C₃ ℤ] [∀ n : ℤ, (shiftFunctor C₃ n).Additive] [∀ n : ℤ, (shiftFunctor C₃ n).Linear R₃]
  [Pretriangulated C₃] [IsTriangulated C₃]
  {F : C₁ ⥤ C₂} [F.CommShift ℤ] [F.IsTriangulated]
  {hF : ∀ X, torsion M₁ C₁ X → torsion M₂ C₂ (F.obj X)}
  {G : C₂ ⥤ C₃} [G.CommShift ℤ] [G.IsTriangulated]
  {hG : ∀ X, torsion M₂ C₂ X → torsion M₃ C₃ (G.obj X)}
  {H : C₁ ⥤ C₃} [H.CommShift ℤ] [H.IsTriangulated]
  {hH : ∀ X, torsion M₁ C₁ X → torsion M₃ C₃ (H.obj X)}

noncomputable instance liftingComp : Localization.Lifting (Q M₁ C₁) (W M₁ C₁) (F ⋙ G ⋙ Q M₃ C₃)
    (mapOfTorsion M₁ M₂ F hF ⋙ mapOfTorsion M₂ M₃ G hG) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₂ C₂) _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (Localization.Lifting.iso (Q M₂ C₂) (W M₂ C₂) (G ⋙ Q M₃ C₃) _)⟩

@[simp]
lemma liftingComp_iso_hom_app (X : C₁) :
    (Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F ⋙ G ⋙ Q M₃ C₃)
      (mapOfTorsion M₁ M₂ F hF ⋙ mapOfTorsion M₂ M₃ G hG)).hom.app X =
      (mapOfTorsion M₂ M₃ G hG).map
          ((Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₂ C₂) _).hom.app X) ≫
        (Localization.Lifting.iso (Q M₂ C₂) (W M₂ C₂) (G ⋙ Q M₃ C₃) _).hom.app (F.obj X) := by
  simp [Localization.Lifting.iso]

variable (hF hG hH) in
/-- The isomorphism of induced functors on rationalizations attached to an isomorphism
`F ⋙ G ≅ H`. -/
noncomputable def mapOfTorsionCompIso (α : F ⋙ G ≅ H) :
    mapOfTorsion M₁ M₂ F hF ⋙ mapOfTorsion M₂ M₃ G hG ≅ mapOfTorsion M₁ M₃ H hH :=
  Localization.liftNatIso (Q M₁ C₁) (W M₁ C₁) (F ⋙ G ⋙ Q M₃ C₃) (H ⋙ Q M₃ C₃) _ _
    (Functor.isoWhiskerRight α (Q M₃ C₃))

lemma mapOfTorsionCompIso_hom_app (α : F ⋙ G ≅ H) (X : C₁) :
    (mapOfTorsionCompIso hF hG hH α).hom.app ((Q M₁ C₁).obj X) =
      (mapOfTorsion M₂ M₃ G hG).map
          ((Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F ⋙ Q M₂ C₂) _).hom.app X) ≫
        (Localization.Lifting.iso (Q M₂ C₂) (W M₂ C₂) (G ⋙ Q M₃ C₃) _).hom.app (F.obj X) ≫
        (Q M₃ C₃).map (α.hom.app X) ≫
        (Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (H ⋙ Q M₃ C₃) _).inv.app X := by
  simp [mapOfTorsionCompIso, Localization.liftNatTrans_app]

end Comp

section Cocycle

variable {M₁ M₂} {R₃ : Type w₃} [CommRing R₃] {M₃ : Submonoid R₃}
  {C₃ : Type u₃} [Category.{v₃} C₃] [Preadditive C₃] [Linear R₃ C₃] [HasZeroObject C₃]
  [HasShift C₃ ℤ] [∀ n : ℤ, (shiftFunctor C₃ n).Additive] [∀ n : ℤ, (shiftFunctor C₃ n).Linear R₃]
  [Pretriangulated C₃] [IsTriangulated C₃]
  {R₄ : Type w₄} [CommRing R₄] {M₄ : Submonoid R₄}
  {C₄ : Type u₄} [Category.{v₄} C₄] [Preadditive C₄] [Linear R₄ C₄] [HasZeroObject C₄]
  [HasShift C₄ ℤ] [∀ n : ℤ, (shiftFunctor C₄ n).Additive] [∀ n : ℤ, (shiftFunctor C₄ n).Linear R₄]
  [Pretriangulated C₄] [IsTriangulated C₄]
  {F₁ : C₁ ⥤ C₂} [F₁.CommShift ℤ] [F₁.IsTriangulated]
  {h₁ : ∀ X, torsion M₁ C₁ X → torsion M₂ C₂ (F₁.obj X)}
  {F₂ : C₂ ⥤ C₃} [F₂.CommShift ℤ] [F₂.IsTriangulated]
  {h₂ : ∀ X, torsion M₂ C₂ X → torsion M₃ C₃ (F₂.obj X)}
  {F₃ : C₃ ⥤ C₄} [F₃.CommShift ℤ] [F₃.IsTriangulated]
  {h₃ : ∀ X, torsion M₃ C₃ X → torsion M₄ C₄ (F₃.obj X)}
  {F₁₂ : C₁ ⥤ C₃} [F₁₂.CommShift ℤ] [F₁₂.IsTriangulated]
  {h₁₂ : ∀ X, torsion M₁ C₁ X → torsion M₃ C₃ (F₁₂.obj X)}
  {F₂₃ : C₂ ⥤ C₄} [F₂₃.CommShift ℤ] [F₂₃.IsTriangulated]
  {h₂₃ : ∀ X, torsion M₂ C₂ X → torsion M₄ C₄ (F₂₃.obj X)}
  {F₁₃ : C₁ ⥤ C₄} [F₁₃.CommShift ℤ] [F₁₃.IsTriangulated]
  {h₁₃ : ∀ X, torsion M₁ C₁ X → torsion M₄ C₄ (F₁₃.obj X)}

/-- The isomorphisms of induced functors on rationalizations inherit the cocycle condition. -/
theorem mapOfTorsionCompIso_cocycle (e₁₂ : F₁ ⋙ F₂ ≅ F₁₂) (e₂₃ : F₂ ⋙ F₃ ≅ F₂₃)
    (e : F₁₂ ⋙ F₃ ≅ F₁₃) (e' : F₁ ⋙ F₂₃ ≅ F₁₃)
    (h : Functor.whiskerRight e₁₂.hom F₃ ≫ e.hom = Functor.whiskerLeft F₁ e₂₃.hom ≫ e'.hom) :
    Functor.whiskerRight (mapOfTorsionCompIso h₁ h₂ h₁₂ e₁₂).hom (mapOfTorsion M₃ M₄ F₃ h₃) ≫
        (mapOfTorsionCompIso h₁₂ h₃ h₁₃ e).hom =
      Functor.whiskerLeft (mapOfTorsion M₁ M₂ F₁ h₁) (mapOfTorsionCompIso h₂ h₃ h₂₃ e₂₃).hom ≫
        (mapOfTorsionCompIso h₁ h₂₃ h₁₃ e').hom := by
  refine Localization.natTrans_ext (Q M₁ C₁) (W M₁ C₁) fun X ↦ ?_
  set ι₁ := Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F₁ ⋙ Q M₂ C₂) (mapOfTorsion M₁ M₂ F₁ h₁)
  have hX := congr_app h X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hX ⊢
  have key : (mapOfTorsionCompIso h₂ h₃ h₂₃ e₂₃).hom.app ((mapOfTorsion M₁ M₂ F₁ h₁).obj
      ((Q M₁ C₁).obj X)) = (mapOfTorsion M₃ M₄ F₃ h₃).map ((mapOfTorsion M₂ M₃ F₂ h₂).map
        (ι₁.hom.app X)) ≫ (mapOfTorsionCompIso h₂ h₃ h₂₃ e₂₃).hom.app ((Q M₂ C₂).obj (F₁.obj X)) ≫
        (mapOfTorsion M₂ M₄ F₂₃ h₂₃).map (ι₁.inv.app X) := by
    rw [← cancel_mono ((mapOfTorsion M₂ M₄ F₂₃ h₂₃).map (ι₁.hom.app X)), Category.assoc,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact ((mapOfTorsionCompIso h₂ h₃ h₂₃ e₂₃).hom.naturality (ι₁.hom.app X)).symm
  have hι₃ := (Localization.Lifting.iso (Q M₃ C₃) (W M₃ C₃) (F₃ ⋙ Q M₄ C₄)
    (mapOfTorsion M₃ M₄ F₃ h₃)).hom.naturality (e₁₂.hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at hι₃
  rw [key, mapOfTorsionCompIso_hom_app, mapOfTorsionCompIso_hom_app, mapOfTorsionCompIso_hom_app,
    mapOfTorsionCompIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp_assoc (mapOfTorsion M₃ M₄ F₃ h₃)
    ((Localization.Lifting.iso (Q M₁ C₁) (W M₁ C₁) (F₁₂ ⋙ Q M₃ C₃)
      (mapOfTorsion M₁ M₃ F₁₂ h₁₂)).inv.app X),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← Functor.map_comp_assoc (mapOfTorsion M₂ M₄ F₂₃ h₂₃) (ι₁.inv.app X),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hι₃, ← Functor.map_comp_assoc (Q M₄ C₄) (F₃.map (e₁₂.hom.app X))]
  erw [hX]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end Cocycle

end CategoryTheory.Rationalization
