/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
/-! # The unit equation follows from the tensor square

Source: the unitality axioms of strong monoidal functors and naturality of unitors.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
universe u v w z a b c d va vb vc vd
namespace WeilConjectures
private theorem coreUnit_unique
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (s t : F.CoreMonoidal) (hμ : ∀ X Y, s.μIso X Y = t.μIso X Y) :
    s.εIso = t.εIso := by
  have he (X : C) : s.εIso.hom ▷ F.obj X = t.εIso.hom ▷ F.obj X := by
    apply (cancel_mono ((s.μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom)).1
    simpa only [hμ, Category.assoc] using
      (s.left_unitality X).symm.trans (t.left_unitality X)
  have hh := congrArg
    (fun k ↦ (𝟙 (𝟙_ D) ⊗ₘ s.εIso.hom) ≫ k ≫
      (𝟙 (F.obj (𝟙_ C)) ⊗ₘ s.εIso.inv)) (he (𝟙_ C))
  simp only [← tensorHom_id, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, Iso.hom_inv_id] at hh
  apply Iso.ext
  apply (cancel_epi (ρ_ (𝟙_ D)).hom).1
  simpa only [tensorHom_id, rightUnitor_naturality] using
    congrArg (fun k ↦ k ≫ (ρ_ (F.obj (𝟙_ C))).hom) hh

private theorem unit_of_tensor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] {F G : C ⥤ D}
    [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    (hμ : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ Functor.LaxMonoidal.μ G X Y) :
    Functor.LaxMonoidal.ε F ≫ e.hom.app (𝟙_ C) = Functor.LaxMonoidal.ε G := by
  have h : (Functor.Monoidal.coreMonoidalTransport e).εIso =
      (Functor.CoreMonoidal.ofLaxMonoidal G).εIso := by
    apply coreUnit_unique
    intro X Y
    apply Iso.ext
    simp only [Functor.Monoidal.coreMonoidalTransport, Iso.trans_hom,
      tensorIso_hom, Iso.app_hom, Iso.symm_hom,
      Functor.CoreMonoidal.ofLaxMonoidal, asIso_hom, Functor.Monoidal.μIso_hom]
    rw [hμ]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  exact congrArg Iso.hom h

private theorem oplaxUnit_of_tensor
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    [MonoidalCategory C] [MonoidalCategory D] {F G : C ⥤ D}
    [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    (hδ : ∀ X Y, e.hom.app (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ G X Y =
      Functor.OplaxMonoidal.δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y)) :
    e.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  have hμ (X Y : C) : Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ Functor.LaxMonoidal.μ G X Y := by
    have hh := congrArg (fun k ↦ Functor.LaxMonoidal.μ F X Y ≫ k ≫
      Functor.LaxMonoidal.μ G X Y) (hδ X Y)
    simpa only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id,
      Functor.Monoidal.μ_δ_assoc] using hh
  have hε := unit_of_tensor e hμ
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).1
  rw [← Category.assoc, hε]
  simp only [Functor.Monoidal.ε_η]

/-- The tensor equation of an invertible transformation between strong monoidal
composites forces its unit equation. Source: monoidal functor unitality and
naturality of the unitors (blueprint: lem-coef-monoidal-square-unit).

Proof: a strong tensorator determines its unit: left unitality gives equality
of the units after tensoring with F(1), and F(1) is isomorphic to the tensor
unit, so this tensoring is faithful. Transport one strong structure along the
natural isomorphism. The given tensor equation identifies its tensorator with
the other one, so uniqueness identifies their units. Convert back to the
oplax convention by cancelling the invertible tensorators and unit maps. -/
theorem coefficientMonoidalSquareUnit
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    {HC : Cᵒᵖ × C ⥤ C} {HD : Dᵒᵖ × D ⥤ D}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (SC : CoefficientClosedStructure HC) (SD : CoefficientClosedStructure HD)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (μF : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (μG : SC.tensor ⋙ G ≅ G.prod G ⋙ SD.tensor)
    (μU : SA.tensor ⋙ U ≅ U.prod U ⋙ SC.tensor)
    (μV : SB.tensor ⋙ V ≅ V.prod V ⋙ SD.tensor)
    (h : F ⋙ V ≅ U ⋙ G)
    (sF : CoefFiniteHomStrong SA SB F μF) (sG : CoefFiniteHomStrong SC SD G μG)
    (sU : CoefFiniteHomStrong SA SC U μU) (sV : CoefFiniteHomStrong SB SD V μV)
    (ht : ∀ K M : A,
      h.hom.app (SA.tensor.obj (K, M)) ≫ G.map (μU.hom.app (K, M)) ≫
          μG.hom.app (U.obj K, U.obj M) =
        V.map (μF.hom.app (K, M)) ≫ μV.hom.app (F.obj K, F.obj M) ≫
          SD.tensor.map (Prod.mkHom (h.hom.app K) (h.hom.app M))) :
    h.hom.app SA.monoidal.tensorUnit ≫
        G.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SC.monoidal U sU.val).inv ≫
        (@Functor.CoreMonoidal.εIso _ _ SC.monoidal _ _ SD.monoidal G sG.val).inv =
      V.map (@Functor.CoreMonoidal.εIso _ _ SA.monoidal _ _ SB.monoidal F sF.val).inv ≫
        (@Functor.CoreMonoidal.εIso _ _ SB.monoidal _ _ SD.monoidal V sV.val).inv := by
  let := SA.monoidal
  let := SB.monoidal
  let := SC.monoidal
  let := SD.monoidal
  let := sF.val.toMonoidal
  let := sG.val.toMonoidal
  let := sU.val.toMonoidal
  let := sV.val.toMonoidal
  have hδ (K M : A) : h.hom.app (K ⊗ M) ≫
      Functor.OplaxMonoidal.δ (U ⋙ G) K M =
      Functor.OplaxMonoidal.δ (F ⋙ V) K M ≫
        (h.hom.app K ⊗ₘ h.hom.app M) := by
    simpa only [Functor.OplaxMonoidal.comp_δ, Functor.comp_obj,
      Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
      Functor.CoreMonoidal.toOplaxMonoidal_δ, sF.property, sG.property,
      sU.property, sV.property, Iso.app_inv, Iso.symm_inv,
      CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
      Iso.app_hom, Category.assoc] using ht K M
  have hu := oplaxUnit_of_tensor h hδ
  simpa only [Functor.OplaxMonoidal.comp_η, Functor.comp_obj,
    Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal,
    Functor.CoreMonoidal.toOplaxMonoidal_η] using hu

end WeilConjectures
