/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
public import WeilConjectures.WeilSheaf.LowerStar

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Exchange

variable (A : Type u') [Category.{u + 1} A]

lemma lowerStarCongr_inv_app_hom_app {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : W.ProEtᵒᵖ) :
    ((lowerStarCongr A h).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).hom.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_inv, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).hom.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  {ah ai : X ⟶ X} {bh bi : Y ⟶ Y} (hA : ai ≫ ah = 𝟙 X) (hB : bi ≫ bh = 𝟙 Y)
  (c : ah ≫ p = p ≫ bh) (c' : p ≫ bi = ai ≫ p)

set_option maxHeartbeats 1000000 in
lemma lowerStar_map_lowerStarComp_trans_inv_app_comp (M : Sheaf (ProEt.topology X) A) :
    (p)_*[A].map ((lowerStarComp A ai ah ≪≫ lowerStarCongr A hA ≪≫ lowerStarId A X).inv.app M) ≫
        (lowerStarComp A ah p).hom.app ((ai)_*[A].obj M) ≫
        (lowerStarCongr A c).hom.app ((ai)_*[A].obj M) ≫
        (lowerStarComp A p bh).inv.app ((ai)_*[A].obj M) =
      (lowerStarComp A bi bh ≪≫ lowerStarCongr A hB ≪≫ lowerStarId A Y).inv.app
          ((p)_*[A].obj M) ≫
        (bh)_*[A].map ((lowerStarComp A p bi).hom.app M ≫ (lowerStarCongr A c').hom.app M ≫
          (lowerStarComp A ai p).inv.app M) := by
  ext V
  simp only [Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStarCongr_inv_app_hom_app,
    lowerStarId_inv_app_hom_app, lowerStar_map_hom_app', lowerStar_obj_obj_map',
    ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId,
      MorphismProperty.Over.pullbackCongr]
  rw [pullback.condition_assoc, hA, Category.comp_id]

end Exchange

end AlgebraicGeometry.ProEtale
