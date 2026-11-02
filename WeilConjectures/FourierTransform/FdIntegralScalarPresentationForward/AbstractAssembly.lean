/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-! # Assembly of the forward coherence from the representative formula

Abstract bookkeeping: a comparison which is, on every object, the inverse of a derived
square followed by an ordinary-to-completed comparison, inherits the cocycle and unit
equations of the derived square and of the completed associator and unit.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace WeilConjectures.FdIntegralScalarForward

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {DE : Type u₁} {DL : Type u₂} {DM : Type u₃} {AE : Type u₄} {AL : Type u₅}
  {AM : Type u₆} [Category.{v₁} DE] [Category.{v₂} DL] [Category.{v₃} DM]
  [Category.{v₄} AE] [Category.{v₅} AL] [Category.{v₆} AM]

/-- Associativity of a comparison given by the representative formula. -/
theorem assoc_assembly
    (SE : ObjectProperty DE) (SL : ObjectProperty DL) (SM : ObjectProperty DM)
    (PE : ObjectProperty AE) (PL : ObjectProperty AL) (PM : ObjectProperty AM)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory)
    (IL : SL.FullSubcategory ⥤ PL.FullSubcategory)
    (IM : SM.FullSubcategory ⥤ PM.FullSubcategory)
    (TE : DE ⥤ AE) (TL : DL ⥤ AL) (TM : DM ⥤ AM)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE) (θL : IL ⋙ PL.ι ≅ SL.ι ⋙ TL)
    (θM : IM ⋙ PM.ι ≅ SM.ι ⋙ TM)
    (Sh : DE ⥤ DL) (Sk : DL ⥤ DM) (Shk : DE ⥤ DM)
    (hSh : ∀ K, SL ((SE.ι ⋙ Sh).obj K)) (hSk : ∀ K, SM ((SL.ι ⋙ Sk).obj K))
    (hShk : ∀ K, SM ((SE.ι ⋙ Shk).obj K))
    (Xh : AE ⥤ AL) (Xk : AL ⥤ AM) (Xhk : AE ⥤ AM)
    (hXh : ∀ K, PL ((PE.ι ⋙ Xh).obj K)) (hXk : ∀ K, PM ((PL.ι ⋙ Xk).obj K))
    (hXhk : ∀ K, PM ((PE.ι ⋙ Xhk).obj K))
    (bh : IE ⋙ PL.lift (PE.ι ⋙ Xh) hXh ≅ SL.lift (SE.ι ⋙ Sh) hSh ⋙ IL)
    (bk : IL ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅ SM.lift (SL.ι ⋙ Sk) hSk ⋙ IM)
    (bhk : IE ⋙ PM.lift (PE.ι ⋙ Xhk) hXhk ≅ SM.lift (SE.ι ⋙ Shk) hShk ⋙ IM)
    (aU : SL.lift (SE.ι ⋙ Sh) hSh ⋙ SM.lift (SL.ι ⋙ Sk) hSk ≅ SM.lift (SE.ι ⋙ Shk) hShk)
    (aC : PL.lift (PE.ι ⋙ Xh) hXh ⋙ PM.lift (PL.ι ⋙ Xk) hXk ≅
      PM.lift (PE.ι ⋙ Xhk) hXhk)
    (A : Xh ⋙ Xk ≅ Xhk) (hA : ∀ X, (aC.hom.app X).hom = A.hom.app X.obj)
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM) (Oc : Oh ⋙ Ok ≅ Ohk)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (ωh : SE.ι ⋙ Oh ≅ SE.ι ⋙ Sh) (ωk : SL.ι ⋙ Ok ≅ SL.ι ⋙ Sk)
    (ωhk : SE.ι ⋙ Ohk ≅ SE.ι ⋙ Shk)
    (Gh : ∀ K, (bh.hom.app K).hom ≫ θL.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) =
      Xh.map (θE.hom.app K) ≫ eh.inv.app K.obj ≫ TL.map (ωh.hom.app K))
    (Gk : ∀ K, (bk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SL.ι ⋙ Sk) hSk).obj K) =
      Xk.map (θL.hom.app K) ≫ ek.inv.app K.obj ≫ TM.map (ωk.hom.app K))
    (Ghk : ∀ K, (bhk.hom.app K).hom ≫ θM.hom.app ((SM.lift (SE.ι ⋙ Shk) hShk).obj K) =
      Xhk.map (θE.hom.app K) ≫ ehk.inv.app K.obj ≫ TM.map (ωhk.hom.app K))
    (hU : ∀ K, (aU.hom.app K).hom = ωk.inv.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫
      Ok.map (ωh.inv.app K) ≫ Oc.hom.app K.obj ≫ ωhk.hom.app K)
    (hD : ∀ Y, TM.map (Oc.hom.app Y) ≫ ehk.hom.app Y =
      ek.hom.app (Oh.obj Y) ≫ Xk.map (eh.hom.app Y) ≫ A.hom.app (TE.obj Y))
    (K : SE.FullSubcategory) :
    (PM.lift (PL.ι ⋙ Xk) hXk).map (bh.hom.app K) ≫
        bk.hom.app ((SL.lift (SE.ι ⋙ Sh) hSh).obj K) ≫ IM.map (aU.hom.app K) =
      aC.hom.app (IE.obj K) ≫ bhk.hom.app K := by
  have hIM : ∀ {X Y : SM.FullSubcategory} (f : X ⟶ Y),
      (IM.map f).hom = θM.hom.app X ≫ TM.map f.hom ≫ θM.inv.app Y := by
    intro X Y f
    have := θM.hom.naturality f
    simp only [Functor.comp_map, ObjectProperty.ι_map] at this
    rw [← Category.assoc, ← this]
    simp
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  change Xk.map (bh.hom.app K).hom ≫ _ ≫ _ = _
  rw [hIM, hA, hU, (Iso.eq_comp_inv (θL.app _)).2 (Gh K),
    (Iso.eq_comp_inv (θM.app _)).2 (Gk _),
    (Iso.eq_comp_inv (θM.app _)).2 (Ghk K)]
  simp only [Iso.app_inv, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have hD' := hD K.obj
  have hDi : Xk.map (eh.inv.app K.obj) ≫ ek.inv.app (Oh.obj K.obj) ≫
      TM.map (Oc.hom.app K.obj) = A.hom.app (TE.obj K.obj) ≫ ehk.inv.app K.obj := by
    rw [← cancel_mono (ehk.hom.app K.obj)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hD']
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    simp
  have hek := ek.inv.naturality (ωh.hom.app K)
  simp only [Functor.comp_map] at hek
  have hAn := A.hom.naturality (θE.hom.app K)
  simp only [Functor.comp_map] at hAn
  rw [← Xk.map_comp_assoc (θL.inv.app _), Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    ← TM.map_comp_assoc (ωk.hom.app _), Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  erw [reassoc_of% hek]
  rw [← TM.map_comp_assoc (Ok.map (ωh.hom.app K)), ← Ok.map_comp, Iso.hom_inv_id_app,
    Functor.map_id, Functor.map_id, Category.id_comp]
  erw [reassoc_of% hDi]
  erw [reassoc_of% hAn]
  rfl

/-- The unit equation of a comparison given by the representative formula. -/
theorem unit_assembly
    (SE : ObjectProperty DE) (PE : ObjectProperty AE)
    (IE : SE.FullSubcategory ⥤ PE.FullSubcategory) (TE : DE ⥤ AE)
    (θE : IE ⋙ PE.ι ≅ SE.ι ⋙ TE)
    (Sr : DE ⥤ DE) (hSr : ∀ K, SE ((SE.ι ⋙ Sr).obj K))
    (Xr : AE ⥤ AE) (hXr : ∀ K, PE ((PE.ι ⋙ Xr).obj K))
    (br : IE ⋙ PE.lift (PE.ι ⋙ Xr) hXr ≅ SE.lift (SE.ι ⋙ Sr) hSr ⋙ IE)
    (uU : SE.lift (SE.ι ⋙ Sr) hSr ≅ 𝟭 _) (uC : PE.lift (PE.ι ⋙ Xr) hXr ≅ 𝟭 _)
    (Xu : Xr ≅ 𝟭 AE) (hC : ∀ X, (uC.hom.app X).hom = Xu.hom.app X.obj)
    (Or : DE ⥤ DE) (ou : ∀ Y, Or.obj Y ⟶ Y) (er : Or ⋙ TE ≅ TE ⋙ Xr)
    (ωr : SE.ι ⋙ Or ≅ SE.ι ⋙ Sr)
    (Gr : ∀ K, (br.hom.app K).hom ≫ θE.hom.app ((SE.lift (SE.ι ⋙ Sr) hSr).obj K) =
      Xr.map (θE.hom.app K) ≫ er.inv.app K.obj ≫ TE.map (ωr.hom.app K))
    (hU : ∀ K, (uU.hom.app K).hom = ωr.inv.app K ≫ ou K.obj)
    (hD : ∀ Y, er.inv.app Y ≫ TE.map (ou Y) = Xu.hom.app (TE.obj Y))
    (K : SE.FullSubcategory) :
    br.hom.app K ≫ IE.map (uU.hom.app K) = uC.hom.app (IE.obj K) := by
  have hIE : ∀ {X Y : SE.FullSubcategory} (f : X ⟶ Y),
      (IE.map f).hom = θE.hom.app X ≫ TE.map f.hom ≫ θE.inv.app Y := by
    intro X Y f
    have := θE.hom.naturality f
    simp only [Functor.comp_map, ObjectProperty.ι_map] at this
    rw [← Category.assoc, ← this]
    simp
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [hIE, hC, hU, (Iso.eq_comp_inv (θE.app _)).2 (Gr K)]
  simp only [Iso.app_inv, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← TE.map_comp_assoc (ωr.hom.app K), Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  erw [reassoc_of% (hD K.obj)]
  have hn := Xu.hom.naturality (θE.hom.app K)
  simp only [Functor.id_map] at hn
  erw [reassoc_of% hn]
  simp

end WeilConjectures.FdIntegralScalarForward
