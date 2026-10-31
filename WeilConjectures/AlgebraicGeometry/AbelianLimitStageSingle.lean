/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianLimitStageHomology
public import WeilConjectures.AlgebraicGeometry.RelativeDirectImageSheafLimit

/-! # Single-sheaf formulas for the stage diagram

Source: Stacks Tags 0EYM and 0GIU, the pure coefficient base case.
(blueprint: lem-sf-abelian-limit-stage-single).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.AbelianLimitStage

variable {B W : Scheme.{u}}

/-- The ordinary single-sheaf image object attached to a stage. -/
noncomputable abbrev singleStage (α : LimitStage B W)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :=
  (upperStar AddCommGrpCat.{u + 1} α.π).obj
    (relativeSheafHigherImage α.g ((upperStar AddCommGrpCat.{u + 1} α.w).obj F) p)

/-- The derived stage object for a sheaf in degree zero has the ordinary
higher-direct-image interpretation. -/
noncomputable def singleStageIso (α : LimitStage B W)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        ((functor AddCommGrpCat.{u + 1} α).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      singleStage α F p :=
  (((upperStar AddCommGrpCat.{u + 1} α.π).mapDerivedCategoryPlusHomologyFunctorIso p).app _).symm ≪≫
    (upperStar AddCommGrpCat.{u + 1} α.π).mapIso ((DerivedCategory.Plus.homologyFunctor _ p).mapIso
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} α.g).mapIso
        (((upperStar AddCommGrpCat.{u + 1} α.w).mapDerivedCategoryPlusSingleFunctor 0).app F)))

/-- The ordinary transition on the single-sheaf stage objects. -/
noncomputable def singleStageMap {α β : LimitStage B W} (φ : LimitStage.Hom α β)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    singleStage β F p ⟶ singleStage α F p :=
  (upperStarComp AddCommGrpCat.{u + 1} α.π φ.s β.π φ.wπ.symm).hom.app
      (relativeSheafHigherImage β.g ((upperStar AddCommGrpCat.{u + 1} β.w).obj F) p) ≫
    (upperStar AddCommGrpCat.{u + 1} α.π).map
      (relativeSheafHigherImageMap ⟨φ.wg⟩ ((upperStar AddCommGrpCat.{u + 1} β.w).obj F)
        ((upperStar AddCommGrpCat.{u + 1} α.w).obj F)
        ((upperStarComp AddCommGrpCat.{u + 1} φ.t β.w α.w φ.ww.symm).inv.app F) p)

private lemma coefficient_single_compat {α β : LimitStage B W}
    (φ : LimitStage.Hom α β) (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} φ.t β.w α.w φ.ww.symm).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
        ((upperStar AddCommGrpCat.{u + 1} α.w).mapDerivedCategoryPlusSingleFunctor 0).hom.app F =
      (upperStar AddCommGrpCat.{u + 1} φ.t).mapDerivedCategoryPlus.map
          (((upperStar AddCommGrpCat.{u + 1} β.w).mapDerivedCategoryPlusSingleFunctor
            0).hom.app F) ≫
        ((upperStar AddCommGrpCat.{u + 1} φ.t).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar AddCommGrpCat.{u + 1} β.w).obj F) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} φ.t β.w α.w φ.ww.symm).inv.app F) := by
  apply (cancel_epi ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} φ.t β.w α.w φ.ww.symm).hom.app
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% upperStarCompDerivedPlus_single]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]


/-- Under the single-sheaf identifications, the derived transition is the
ordinary higher-image transition of Tag 0EYM.

Proof: use the exact-pullback homology comparison to move the outer pullbacks
past homology. Naturality of that comparison and of the square exchange moves
the coefficient single isomorphism to the source side. Compatibility of inverse-image
composition with single complexes identifies the coefficient map with the ordinary
pullback transition. These are exactly the factors in the displayed ordinary map.
Source: Stacks Tag 0GIU, reduction of the shifted-sheaf case to Tag 0EYM.
(blueprint: lem-sf-abelian-limit-stage-single). -/
lemma singleStageIso_naturality {α β : LimitStage B W}
    (φ : LimitStage.Hom α β) (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
        ((transition AddCommGrpCat.{u + 1} φ).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
        (singleStageIso α F p).hom =
      (singleStageIso β F p).hom ≫ singleStageMap φ F p := by
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let σβ := ((upperStar AddCommGrpCat.{u + 1} β.w).mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  let σα := ((upperStar AddCommGrpCat.{u + 1} α.w).mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  let Rβ := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} β.g
  let Rα := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} α.g
  let Hα := DerivedCategory.Plus.homologyFunctor
    (Sheaf α.S.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)
  let Hβ := DerivedCategory.Plus.homologyFunctor
    (Sheaf β.S.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℤ)
  apply (cancel_epi
    (((upperStar AddCommGrpCat.{u + 1} β.π).mapDerivedCategoryPlusHomologyFunctorIso
      p).hom.app
    (Rβ.obj ((upperStar AddCommGrpCat.{u + 1} β.w).mapDerivedCategoryPlus.obj K)))).mp
  simp only [singleStageIso, K, Rβ, rightDerivedLowerStarPlus,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc]
  have ht := transition_homology AddCommGrpCat.{u + 1} φ K p
  dsimp only [K, rightDerivedLowerStarPlus] at ht
  rw [← Category.assoc, ht]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  dsimp only [singleStage, singleStageMap, relativeSheafHigherImage,
    relativeSheafHigherImageMap, rightDerivedLowerStarPlus, Functor.comp_obj]
  have hπ := (upperStarComp AddCommGrpCat.{u + 1} α.π φ.s β.π φ.wπ.symm).hom.naturality
    (Hβ.map (Rβ.map σβ))
  dsimp only [Functor.comp_map, Functor.comp_obj, Hβ, Rβ, σβ, rightDerivedLowerStarPlus] at hπ
  rw [reassoc_of% hπ]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  have hn :=
    ((upperStar AddCommGrpCat.{u + 1} φ.s).mapDerivedCategoryPlusHomologyFunctorIso
      p).hom.naturality
    (Rβ.map σβ)
  have hb := (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} ⟨φ.wg⟩).naturality σβ
  have hc := congrArg (fun f ↦ Rα.map f) (coefficient_single_compat φ F)
  dsimp only [Functor.comp_map, Functor.comp_obj, Rβ, σβ,
    rightDerivedLowerStarPlus] at hn hb
  rw [reassoc_of% hn]
  rw [← Hα.map_comp]
  congr 1
  congr 1
  apply Hα.congr_map
  dsimp only [Rα, Rβ, rightDerivedLowerStarPlus] at hb hc ⊢
  simp only [Functor.map_comp] at hc ⊢
  rw [reassoc_of% hb]
  rw [← hc]

/-- Postcomposition of the coefficient map commutes with the higher-image square map.
Source: Stacks Tag 0EYM, naturality of the canonical coefficient map.
(blueprint: lem-sf-abelian-limit-stage-single). -/
lemma relativeSheafHigherImageMap_postcomp
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G H : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ G) (ψ : G ⟶ H) (p : ℕ) :
    relativeSheafHigherImageMap sq F G φ p ≫
        (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).map
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
            ((DerivedCategory.Plus.singleFunctor _ 0).map ψ)) =
      relativeSheafHigherImageMap sq F H (φ ≫ ψ) p := by
  simp only [relativeSheafHigherImageMap, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale.AbelianLimitStage
