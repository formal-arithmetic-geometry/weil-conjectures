/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Identity normalization of the specified iterated pullback structure. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem exactUnitor_comp
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ C) (G H : C ⥤ D) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : H ≅ F ⋙ G) (a : F ≅ 𝟭 C) (d : H ≅ G)
    (hd : c ≪≫ Functor.isoWhiskerRight a G ≪≫ Functor.leftUnitor G = d)
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso c).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app K ≫
        G.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso a).hom.app K ≫
          (Functor.mapDerivedCategoryIdIso C).hom.app K) =
      (Functor.mapDerivedCategoryNatIso d).hom.app K := by
  have hn := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight a G) K
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_id_comp G) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  have ht := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) hd
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at ht
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn]
  rw [hu]
  erw [Category.comp_id]
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor G)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  simpa only [hi, NatTrans.id_app, Category.comp_id] using ht

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
open CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem derived_upperStarCongr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (w : f = g) (K : D Λ Y) :
    (Functor.mapDerivedCategoryNatIso (upperStarCongr Λ w)).hom.app K =
      eqToHom (congrArg (fun a : X ⟶ Y ↦ (P Λ a).obj K) w) := by
  subst g
  simp only [upperStarCongr_self, Functor.mapDerivedCategoryNatIso_refl,
    NatTrans.id_app, eqToHom_refl]

private theorem pComp_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (K : D Λ Y) :
    (pComp Λ f (𝟙 Y)).hom.app K ≫ (P Λ f).map ((pId Λ Y).hom.app K) =
      eqToHom (congrArg (fun a : X ⟶ Y ↦ (P Λ a).obj K) (Category.comp_id f)) := by
  have hd : upperStarComp Λ f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (upperStarId Λ Y) (upperStar Λ f) ≪≫
      Functor.leftUnitor (upperStar Λ f) = upperStarCongr Λ (Category.comp_id f) := by
    rw [upperStarComp_id_right]
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_hom_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have h := exactUnitor_comp (upperStar Λ (𝟙 Y)) (upperStar Λ f)
    (upperStar Λ (f ≫ 𝟙 Y)) (upperStarComp Λ f (𝟙 Y)) (upperStarId Λ Y)
    (upperStarCongr Λ (Category.comp_id f)) hd K
  simpa only [pComp, pId, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
    h.trans (derived_upperStarCongr Λ (Category.comp_id f) K)

/-- The degree-one structure is the original structure, with equality transport.
Source: the identity and composition normalization in the compact-return power-law proof.
(blueprint: lem-fd-condensed-iterate-structure-one).

Proof: the right unit law for ordinary pullback composition passes to exact derived
functors by the map-derived composition and identity laws. In the recursion at one,
this unit comparison cancels the identity structure and the power equality transport. -/
theorem iterateStructure_one {T : Scheme.{u}} (f : End T) {K : D Λ T}
    (θ : (P Λ f).obj K ≅ K) :
    (iterateStructure Λ f θ 1).hom =
      eqToHom (congrArg (fun a : End T ↦ (P Λ a).obj K) (pow_one f)) ≫ θ.hom := by
  change eqToHom (congrArg (fun a : End T ↦ (P Λ a).obj K) (pow_succ f 0)) ≫
      (pComp Λ f (𝟙 T)).hom.app K ≫
        (P Λ f).map ((pId Λ T).hom.app K) ≫ θ.hom = _
  rw [reassoc_of% pComp_right_unit Λ f K, eqToHom_trans_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
