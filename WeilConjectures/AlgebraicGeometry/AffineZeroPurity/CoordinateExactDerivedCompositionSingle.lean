/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.Derived.DerivedSingleConstantsComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact coordinate derived composition on the coefficient single -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

attribute [local implicit_reducible] iteratedAffineLine zero
  Scheme.Hom.toIteratedAffineLine AffineSpace.zeroSection cupSingle

attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits

private theorem exact_composition_at
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj X) ≫
      (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj X) ≫
      G.rightDerivedFunctor.map
        (F.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj X)) ≫
      G.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
    H.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj X) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj X) ≫
      (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj X) := by
  apply (cancel_epi (H.rightDerivedFunctorUnit.app X)).mp
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app_assoc,
    Functor.whiskerRight_app]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  have fac (J : C ⥤ E) [J.Additive] [PreservesFiniteLimits J]
      [PreservesFiniteColimits J] := congrArg (fun t ↦ t.app X)
        J.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
  have hF := congrArg (fun t ↦ t.app X)
    F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
  have hG := congrArg (fun t ↦ t.app
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
    G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hF hG
  rw [← G.rightDerivedFunctor.map_comp_assoc, hF,
    G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality]
  simp only [Functor.comp_obj]
  rw [reassoc_of% hG]
  have hH := fac H
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hH
  rw [reassoc_of% hH]
  apply (cancel_mono
    (G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app X) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app X))).mp
  simp only [Category.assoc, Functor.mapDerivedCategoryCompIso_fach,
    Functor.mapDerivedCategoryNatIso_fach]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj]
  erw [G.mapDerivedCategory.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Exact derived composition respects the coordinate coefficient single comparisons.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior-product sentence;
rightDerivedFunctorIsoMapDerivedCategory and singleFunctorCompRightDerivedFunctorIso
in WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/MapDerivedCategory.lean
(blueprint: lem-pur-exact-derived-composition-single).

Proof: characterize the derived compositor and the exact-derived comparison by their
units on the homotopy category. The unit identities identify their composite with the
canonical mapDerivedCategory composition comparison. Apply this equality on the single
complex of M. Expand mapDerivedCategorySingleFunctor through the cochain single functor
and localization Q. Functoriality of Q, and the componentwise composition comparison
for maps of complexes, reduce the equation to e.hom.app M in degree zero and zero maps
in every other degree. Naturality in the isomorphism e gives the asserted transport.
Identify the coefficient unit with the single complex using unit_single_eq. Only
exactness of the three direct images enters: no origin compositor or proper comparison
is used. The rank-zero identity case and zero objects obey these same component laws. -/
theorem coordinate_exact_derived_composition_single
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ)
    [PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r))]
    [PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (lastSection B r))]
    [PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B (r + 1)))] :
  let A := (setting P n).Coefficient
  let f := zero B r
  let g := lastSection B r
  let h := zero B (r + 1)
  let q : h = f ≫ g := (CoordinateTowerNormalization.zero_successor B r).symm
  let F := lowerStar (ModuleCat.{u + 1} A) f
  let G := lowerStar (ModuleCat.{u + 1} A) g
  let H := lowerStar (ModuleCat.{u + 1} A) h
  letI : F.PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  let e : H ≅ F ⋙ G := lowerStarCongr (ModuleCat.{u + 1} A) q ≪≫
    (lowerStarComp (ModuleCat.{u + 1} A) f g).symm
  let K := unit P n B
  let M := (setting P n).constant B
  let sf := F.rightDerivedFunctorIsoMapDerivedCategory.app K ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app M
  let sg := G.rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor _ 0).obj (F.obj M)) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (F.obj M)
  let sh := H.rightDerivedFunctorIsoMapDerivedCategory.app K ≪≫
    (H.mapDerivedCategorySingleFunctor 0).app M
  ((Functor.rightDerivedFunctorNatIso e) ≪≫
      Functor.rightDerivedFunctorCompIso F G).hom.app K ≫
      G.rightDerivedFunctor.map sf.hom ≫ sg.hom =
    sh.hom ≫ (DerivedCategory.singleFunctor _ 0).map (e.hom.app M) := by
  dsimp only
  let A := (setting P n).Coefficient
  let F := lowerStar (ModuleCat.{u + 1} A) (zero B r)
  let G := lowerStar (ModuleCat.{u + 1} A) (lastSection B r)
  let H := lowerStar (ModuleCat.{u + 1} A) (zero B (r + 1))
  let : F.PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (zero B r)).preservesKInjectiveComplexes
  let e : H ≅ F ⋙ G := lowerStarCongr (ModuleCat.{u + 1} A)
    (CoordinateTowerNormalization.zero_successor B r).symm ≪≫
    (lowerStarComp (ModuleCat.{u + 1} A) (zero B r) (lastSection B r)).symm
  let M := (setting P n).constant B
  have hm :
      (Functor.rightDerivedFunctorNatIso e).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (Functor.rightDerivedFunctorCompIso F G).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        G.rightDerivedFunctor.map
          ((F.rightDerivedFunctorIsoMapDerivedCategory.hom.app
              ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
            (F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        G.rightDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (F.obj M)) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) =
      H.rightDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor _ 0).map (e.hom.app M) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
    have hc := exact_composition_at F G H e
      (((HomotopyCategory.singleFunctors _).functor 0).obj M)
    simp only [DerivedCategory.Qh_obj_singleFunctors_obj] at hc
    rw [reassoc_of% hc]
    congr 1
    have hs := Functor.derived_single_constants_comparison F G H e.symm M
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm] at hs
    have ht := congrArg (fun t ↦
      (Functor.mapDerivedCategoryNatIso e).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫ t ≫
        (DerivedCategory.singleFunctor _ 0).map (e.hom.app M)) hs
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app] at ht
    simp only [Functor.comp_obj] at ht
    erw [(DerivedCategory.singleFunctor _ 0).map_id] at ht
    simpa only [Category.comp_id] using ht.symm
  dsimp only [A, F, G, H, e, M, Iso.trans, Iso.app, unit, cupSingle] at hm ⊢
  simpa only [NatTrans.comp_app, Category.assoc] using hm

end AlgebraicGeometry.ProEtale.AffineZeroPurity
