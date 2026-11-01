/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumStalks
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSheafProjectionData

/-! # Normalization of the étale projection comparison

Source: Stacks Project, Tag 0GKF.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

private lemma etaleLiftSection_iso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)).inv.app N).hom.app (op W) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) ≫
        ((upperStar (ModuleCat.{u + 1} A) e).obj N).obj.map
          (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
            (inferInstance : Etale e) trivial).unit.app W).op) := by
  let i := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
    (inferInstance : Etale e)
  let j := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ e
    (inferInstance : Etale e) trivial
  apply (cancel_mono ((i.hom.app N).hom.app (op W))).mp
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e)
    (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)) N
  have huW := congr_app (Sheaf.hom_ext_iff.1 hu)
    (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
  rw [Category.assoc]
  erw [(i.hom.app N).hom.naturality (j.unit.app W).op]
  change _ =
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e).unit.app N).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) ≫
      (i.hom.app N).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ e).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))) ≫ _
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at huW
  erw [huW]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  change _ = N.obj.map (j.counit.app _).op ≫
    N.obj.map ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).map
      (j.unit.app W)).op
  rw [← N.obj.map_comp]
  rw [← op_comp]
  erw [j.left_triangle_components W]
  change _ = N.obj.map (𝟙 (op ((MorphismProperty.Over.map ⊤
    (inferInstance : Etale e)).obj W)))
  rw [N.obj.map_id]
  exact congr_app (Sheaf.hom_ext_iff.1 (i.inv_hom_id_app N)) (op W)

private lemma projection_sum_unit (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
    ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M).hom.app
        (op W) =
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lanUnit.app M.obj).app
        (op W) ≫
      (toSheafify T.smallEtaleTopology
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lan.obj M.obj)).app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) := by
  change ((sheafToPresheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).map
    ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M)).app
      (op W) = _
  unfold etaleLowerShriekAdjunction
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map,
    Iso.refl_hom, NatTrans.id_app,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  dsimp only [Functor.comp_map, ObjectProperty.ι_map, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, ObjectProperty.FullSubcategory.id_hom]
  simp only [NatTrans.id_app]
  erw [Category.comp_id]

@[reassoc]
private lemma projection_sum_naturality (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    {M M' : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)} (f : M ⟶ M')
    (W : V.Etale) :
    ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M).hom.app
        (op W) ≫
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).map f).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) =
      f.hom.app (op W) ≫
      ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app M').hom.app
        (op W) := by
  exact (congr_app (Sheaf.hom_ext_iff.1
    ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.naturality f))
      (op W)).symm

@[reassoc]
private lemma projection_sheafification_unit (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (P : V.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (W : V.Etale) :
    (toSheafify V.smallEtaleTopology P).app (op W) ≫
        ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app
          ((presheafToSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj P)).hom.app
            (op W) ≫
        ((presheafToSheafCompEtaleLowerShriekIso (ModuleCat.{u + 1} A)
          (inferInstance : Etale e)).hom.app P).hom.app
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) =
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lanUnit.app P).app
          (op W) ≫
        (toSheafify T.smallEtaleTopology
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lan.obj P)).app
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    ((sheafificationAdjunction V.smallEtaleTopology (ModuleCat.{u + 1} A)).comp
      (etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance))
    ((((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op.lanAdjunction
      (ModuleCat.{u + 1} A)).comp
      (sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A))).ofNatIsoRight
        (Iso.refl _)) P
  have huW := NatTrans.congr_app hu (op W)
  simpa only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    sheafificationAdjunction_unit_app, Functor.comp_map, ObjectProperty.ι_map,
    Functor.whiskerLeft_app, Functor.whiskeringLeft_obj_map, NatTrans.comp_app,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Functor.lanAdjunction_unit,
    Category.assoc, Functor.sheafPushforwardContinuous_map_hom,
    localizationRestriction, presheafToSheafCompEtaleLowerShriekIso] using! huW

private lemma projection_tensor_unit (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    letI := adj.rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ R M N ≫
        (tensorIso (asIso (adj.counit.app M)).symm
          (asIso (adj.counit.app N)).symm ≪≫
            Functor.Monoidal.μIso L M.obj N.obj).hom.hom =
      toSheafify X.smallEtaleTopology (M.obj ⊗ N.obj) := by
  dsimp only
  let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
  change adj.unit.app (M.obj ⊗ N.obj) ≫
    R.map (Functor.OplaxMonoidal.δ L _ _ ≫
      (adj.counit.app M ⊗ₘ adj.counit.app N)) ≫
    R.map (inv (adj.counit.app M) ⊗ₘ inv (adj.counit.app N)) ≫
    R.map (Functor.LaxMonoidal.μ L M.obj N.obj) = adj.unit.app (M.obj ⊗ N.obj)
  rw [← R.map_comp, ← R.map_comp]
  have he : (Functor.OplaxMonoidal.δ L M.obj N.obj ≫
      (adj.counit.app M ⊗ₘ adj.counit.app N)) ≫
      ((inv (adj.counit.app M) ⊗ₘ inv (adj.counit.app N)) ≫
        Functor.LaxMonoidal.μ L M.obj N.obj) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (adj.counit.app M ⊗ₘ adj.counit.app N),
      tensorHom_comp_tensorHom, IsIso.hom_inv_id, IsIso.hom_inv_id, id_tensorHom_id,
      Category.id_comp, Functor.Monoidal.δ_μ]
  rw [he, R.map_id]
  exact Category.comp_id _

private lemma projection_mixed_tensor_unit (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    letI := adj.rightAdjointLaxMonoidal
    toSheafify X.smallEtaleTopology (P ⊗ N.obj) ≫
      R.map (Functor.OplaxMonoidal.δ L P N.obj) ≫
      R.map (𝟙 (L.obj P) ⊗ₘ adj.counit.app N) =
    (toSheafify X.smallEtaleTopology P ⊗ₘ 𝟙 N.obj) ≫
      Functor.LaxMonoidal.μ R (L.obj P) N := by
  dsimp only
  let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let := adj.rightAdjointLaxMonoidal
  change adj.unit.app (P ⊗ R.obj N) ≫ R.map (Functor.OplaxMonoidal.δ L P (R.obj N)) ≫
    R.map (𝟙 (L.obj P) ⊗ₘ adj.counit.app N) = _
  rw [adj.unit_app_tensor_comp_map_δ_assoc]
  rw [← Functor.LaxMonoidal.μ_natural]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, adj.right_triangle_components]
  rfl

private lemma projection_forward_unit (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale) :
    letI := (sheafificationAdjunction V.smallEtaleTopology
      (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
    letI := (sheafificationAdjunction T.smallEtaleTopology
      (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
    (Functor.LaxMonoidal.μ (sheafToPresheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      M ((upperStar (ModuleCat.{u + 1} A) e).obj N)).app (op W) ≫
      ((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app
        (M ⊗ (upperStar (ModuleCat.{u + 1} A) e).obj N)).hom.app (op W) ≫
      (etaleLowerShriekTensorIso (ModuleCat.{u + 1} A)
        (inferInstance : Etale e) M N).hom.hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) =
    (((etaleLowerShriekAdjunction (ModuleCat.{u + 1} A) e inferInstance).unit.app
      M).hom.app (op W) ⊗ₘ
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
        (inferInstance : Etale e)).hom.app N).hom.app (op W)) ≫
      (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) N).app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)) := by
  let := (sheafificationAdjunction V.smallEtaleTopology
    (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
  let := (sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
  simp only [etaleLowerShriekTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    tensorIso_hom, Iso.symm_hom, asIso_hom, asIso_inv, whiskerLeftIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  let h := (tensorIso
      (asIso ((sheafificationAdjunction V.smallEtaleTopology
        (ModuleCat.{u + 1} A)).counit.app M)).symm
      (asIso ((sheafificationAdjunction V.smallEtaleTopology
        (ModuleCat.{u + 1} A)).counit.app
          ((upperStar (ModuleCat.{u + 1} A) e).obj N))).symm ≪≫
    Functor.Monoidal.μIso (presheafToSheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} A)) _ _ ≪≫
    (presheafToSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
      (whiskerLeftIso M.obj ((sheafToPresheaf V.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapIso
          ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
            (inferInstance : Etale e)).app N)))).hom
  have hs := projection_sum_naturality A e h W
  simp only [h, Iso.trans_hom, tensorIso_hom, Iso.symm_hom, asIso_inv,
    Functor.mapIso_hom, whiskerLeftIso_hom] at hs
  erw [reassoc_of% hs]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have ht := NatTrans.congr_app (projection_tensor_unit A V M
    ((upperStar (ModuleCat.{u + 1} A) e).obj N)) (op W)
  simp only [NatTrans.comp_app, Iso.trans_hom, tensorIso_hom, Iso.symm_hom, asIso_inv,
    ObjectProperty.FullSubcategory.comp_hom] at ht
  simp only [Category.assoc]
  erw [reassoc_of% ht]
  let g := M.obj ◁ (sheafToPresheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).map
    ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)).app N).hom
  have hn := NatTrans.congr_app (toSheafify_naturality V.smallEtaleTopology g) (op W)
  simp only [NatTrans.comp_app] at hn
  erw [reassoc_of% hn.symm]
  have hsn := projection_sheafification_unit A e
    (M.obj ⊗ ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op ⋙ N.obj)) W
  erw [reassoc_of% hsn]
  let b := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).op
  have hnp := NatTrans.congr_app
    (toSheafify_naturality T.smallEtaleTopology (b.lanProjectionMap M.obj N.obj))
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
  simp only [NatTrans.comp_app] at hnp
  erw [reassoc_of% hnp.symm]
  erw [reassoc_of% (b.lanUnit_app_comp_lanProjectionMap_app M.obj N.obj (op W))]
  have hm := NatTrans.congr_app (projection_mixed_tensor_unit A T (b.lan.obj M.obj) N)
    (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
  simp only [NatTrans.comp_app] at hm
  simp only [Functor.Monoidal.μIso_inv, ← id_tensorHom]
  erw [hm]
  dsimp only [g, Monoidal.whiskerLeft_app]
  simp only [← id_tensorHom, Monoidal.tensorHom_app, NatTrans.id_app]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rw [projection_sum_unit A e M W]
  rfl

/-- The inverse of the canonical Kan-extension projection comparison has the prescribed
formula on a summand section and a target section.

Source: Stacks Project, Tag 0GKF, pure-tensor construction, with Tags 03S5 and 0GMW
(blueprint: lem-pur-etale-projection-section-normalization).

Proof: apply the forward isomorphism to the proposed equality. The tensor comparison
of sheafification identifies the tensor of the two sheafification units with the unit
of the presheaf tensor. The comparison commuting sum extension with sheafification is
fixed by its adjunction unit equation. Naturality moves the source tensor comparison
and the inverse-image restriction comparison through the Kan-extension unit. The
Kan-extension projection map then sends this unit to the unit on M tensored with the
identity on N, by lanUnit_app_comp_lanProjectionMap_app. The sheafification counit on N
cancels its unit. Finally upperStarIsoLocalizationRestriction.inv is the inverse-image
unit followed by graph restriction: its hom is fixed by the adjunction unit equation,
and restriction along the graph cancels the site counit by the triangle identity.
Thus both sides have the same image under an isomorphism. No lift, nonzero section,
flatness or finiteness hypothesis is used. -/
theorem etaleProjection_section_normalization (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e]
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale)
    (m : M.obj.obj (op W))
    (n : N.obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))) :
    (etaleLowerShriekTensorIso (ModuleCat.{u + 1} A)
        (inferInstance : Etale e) M N).inv.hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
        (etaleSheafTensorSection A _ N
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
          (etaleSumSection A e M W m) n) =
      etaleSumSection A e _ W
        (etaleSheafTensorSection A M _ W m (etaleLiftSection A e N W n)) := by
  let i := etaleLowerShriekTensorIso (ModuleCat.{u + 1} A)
    (inferInstance : Etale e) M N
  let Z := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W
  let j := ((sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso i).app
    (op Z)
  apply j.toLinearEquiv.injective
  have hi := congrArg (fun f ↦ f
    (etaleSheafTensorSection A _ N Z (etaleSumSection A e M W m) n)) j.inv_hom_id
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hi
  change j.hom (j.inv _) = j.hom _
  rw [hi]
  have h := congrArg (fun f ↦ f (m ⊗ₜ[A] etaleLiftSection A e N W n))
    (projection_forward_unit A e M N W)
  simp only [ModuleCat.comp_apply] at h
  have hu := projection_sum_unit A e M W
  have hq := projection_sum_unit A e
    (etaleSheafTensor A V M ((upperStar (ModuleCat.{u + 1} A) e).obj N)) W
  erw [hu, hq] at h
  have hl := etaleLiftSection_iso A e N W
  have hl' : ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)).inv.app N).hom.app (op W) n =
      etaleLiftSection A e N W n := congrArg (fun f ↦ f n) hl
  rw [← hl'] at h
  have hi' := congrArg (fun f ↦ f n) (congr_app
    (Sheaf.hom_ext_iff.1 ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
      (inferInstance : Etale e)).inv_hom_id_app N)) (op W))
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.comp_app, ModuleCat.comp_apply, NatTrans.id_app, ModuleCat.id_apply] at hi'
  change j.hom (etaleSumSection A e _ W
    (etaleSheafTensorSection A M _ W m
      (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
        (inferInstance : Etale e)).inv.app N).hom.app (op W) n))) =
    etaleSheafTensorSection A _ N Z (etaleSumSection A e M W m)
      (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
        (inferInstance : Etale e)).hom.app N).hom.app (op W)
          (((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) e
            (inferInstance : Etale e)).inv.app N).hom.app (op W) n)) at h
  rw [hi', hl'] at h
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The composite involves two sheafification monoidal comparisons and adjunction units.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.Etale
