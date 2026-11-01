/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentStalk
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.CospecializationSections

/-! # The canonical finite-stalk comparison and geometric pullback

Source: inverse-image coherence and finite-level comparison in the proof of
real condensed fibre functoriality.
(blueprint: lem-real-condensed-fibre-pullback-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RealCondensedFibre

set_option maxHeartbeats 800000 in
-- Unit and germ comparisons contain large dependent site-point types.
private theorem etale_stalk_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (h : Z ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (pointSmallEtale z).sheafFiber.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} h f).hom.app F) ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} h z).hom.app
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F) ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f (z ≫ h)).hom.app F ≫
      eqToHom (congrArg (fun w ↦ (pointSmallEtale w).sheafFiber.obj F)
        (Category.assoc z h f)) =
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (h ≫ f) z).hom.app F := by
  apply (cancel_epi
    ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (h ≫ f) z).inv.app F)).mp
  rw [Iso.inv_hom_id_app]
  apply (pointSmallEtale (z ≫ h ≫ f)).presheafFiber_hom_ext
  intro U v
  erw [reassoc_of% (Etale.toPresheafFiber_upperStarCompSheafFiberIso_inv
    AddCommGrpCat.{u + 1} (h ≫ f) z F U v)]
  erw [show (pointSmallEtale z).sheafFiber.map _ =
    (pointSmallEtale z).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  have hu := congrArg (fun a ↦ a.hom.app (op U))
    (Etale.upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} h f F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app] at hu
  rw [Etale.lowerStarComp_hom_app_hom_app] at hu
  erw [reassoc_of% hu]
  let b := (MorphismProperty.Over.pullbackComp h f (h ≫ f) rfl).hom.app U
  let v₀ := (pointSmallEtaleFiberEtaleIso (h ≫ f) z).inv.app U v
  have hb := Etale.eq_homToPullback h b
  have hh := Etale.unit_app_map_toPresheafFiber_upperStarCompSheafFiberIso_hom
    AddCommGrpCat.{u + 1} h ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F) z
    (b.left ≫ pullback.fst (f.Etale.obj U).hom h)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ h) (MorphismProperty.Over.w b)) v₀
  erw [← hb] at hh
  erw [reassoc_of% hh]
  let v' : (pointSmallEtale ((z ≫ h) ≫ f)).fiber.obj U :=
    Over.homMk v.left (by
      change v.left ≫ U.hom = (z ≫ h) ≫ f
      exact (Over.w v).trans (Category.assoc z h f).symm)
  have hv₁ :
      Over.homMk (U := Over.mk (z ≫ h))
          (V := (Scheme.Etale.forget Y).obj (f.Etale.obj U))
          (v₀.left ≫ b.left ≫ pullback.fst (f.Etale.obj U).hom h)
          (Etale.fiber_left_comp_comp_hom_eq h z
            (by rw [Category.assoc, pullback.condition, ← Category.assoc]
                exact congrArg (· ≫ h) (MorphismProperty.Over.w b)) v₀) =
        (pointSmallEtaleFiberEtaleIso f (z ≫ h)).inv.app U v' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (v₀.left ≫ b.left ≫ pullback.fst (pullback.snd U.hom f) h) ≫
          pullback.fst U.hom f = _
      rw [Category.assoc, Category.assoc,
        MorphismProperty.Over.pullbackComp_left_fst_fst]
      erw [pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      exact (pointSmallEtaleFiberEtaleIso_inv_app_left_fst f (z ≫ h) U v').symm
    · exact (Over.w _).trans (Over.w _).symm
  erw [hv₁,
    Etale.unit_app_toPresheafFiber_upperStarCompSheafFiberIso_hom_assoc]
  erw [Category.comp_id]


private theorem stalk_point_congr
    {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {a b : Spec (.of Ω) ⟶ Y} (h : a = b)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)) h) ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f b).hom.app F =
    (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f a).hom.app F ≫
      eqToHom (congrArg (fun z ↦ (pointSmallEtale (z ≫ f)).sheafFiber.obj F) h) := by
  subst b
  simp

/-- Final-object germs commute with composition of the specified etale stalk comparisons.
This concerns only etale abelian sheaves, with no pro-etale comparison or module data.

Source: thm-lisse-qlbar-representations, Fibres paragraph; canonical etale
inverse-image unit/germ formulas and inverse-image composition units.
(blueprint: lem-real-condensed-fibre-pullback-comparisons)

Proof in words:
The germ at the identity point and terminal etale neighbourhood of Spec Ω is an
isomorphism, since that pointed neighbourhood is initial. By naturality of germs,
move the etale composition map across the germ on the right, and cancel the
terminal-neighbourhood germ. Precompose with the inverse stalk comparisons so that
the domain is the stalk of F at y followed by f. Test the resulting maps on germs
of sections over pointed etale neighbourhoods. The inverse unit-germ formula
expresses both inverse stalk comparisons by the units and lifted neighbourhoods.
Apply it twice, and use the unit identity for composition of etale inverse images.
The resulting germs coincide: both come from the original section over the same
neighbourhood, and the point lifts agree by the fibre-product universal property.
The stalk colimit universal property identifies the morphisms. The identification
of a point composed with the identity contributes the two displayed eqToHom
factors; these agree on germs, hence on the stalk. This proves the equality for the
specified adjunction-normalized comparisons. The argument requires no finiteness
assumption and applies to the zero sheaf and identity morphisms. -/
theorem etale_final_germ_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 _)) (Over.homMk (𝟙 _) (by simp))
        ((Etale.upperStar AddCommGrpCat.{u + 1} y).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)).obj ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} y (𝟙 _)).hom.app
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F) ≫
      eqToHom (congrArg (fun z ↦ (Scheme.pointSmallEtale z).sheafFiber.obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)) (Category.id_comp y)) ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f y).hom.app F =
    ((Etale.upperStarComp AddCommGrpCat.{u + 1} y f).inv.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 _))) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 _)) (Over.homMk (𝟙 _) (by simp))
        ((Etale.upperStar AddCommGrpCat.{u + 1} (y ≫ f)).obj F).obj ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} (y ≫ f) (𝟙 _)).hom.app F ≫
      eqToHom (congrArg (fun z ↦ (Scheme.pointSmallEtale z).sheafFiber.obj F)
        (Category.id_comp (y ≫ f))) := by
  let C := (Etale.upperStarComp AddCommGrpCat.{u + 1} y f).app F
  let P := pointSmallEtale (𝟙 (Spec (.of Ω)))
  have hc := etale_stalk_comp f y (𝟙 _) F
  have hp := stalk_point_congr f (Category.id_comp y) F
  have hi :
      eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj F)
          (Category.assoc (𝟙 _) y f)) ≫
        eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj F)
          (Category.id_comp (y ≫ f))) =
      eqToHom (congrArg (fun z ↦ (pointSmallEtale (z ≫ f)).sheafFiber.obj F)
        (Category.id_comp y)) := by
    erw [eqToHom_trans]
  have hc' : P.sheafFiber.map C.inv ≫ P.sheafFiber.map C.hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id]
    exact P.sheafFiber.map_id _
  have he := congrArg (fun a ↦ P.sheafFiber.map C.inv ≫ a ≫
    eqToHom (congrArg (fun z ↦ (pointSmallEtale z).sheafFiber.obj F)
      (Category.id_comp (y ≫ f)))) hc
  simp only [Category.assoc] at he
  erw [reassoc_of% hc', hi, ← hp] at he
  erw [← GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  exact congrArg (fun a ↦ P.toPresheafFiber
    (Scheme.Etale.mk (𝟙 _)) (Over.homMk (𝟙 _) (by simp))
    ((Etale.upperStar AddCommGrpCat.{u + 1} y).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F)).obj ≫ a) he



end AlgebraicGeometry.ProEtale.RealCondensedFibre
