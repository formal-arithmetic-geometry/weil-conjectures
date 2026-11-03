/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianTensorDescent
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement

import all Mathlib.Logic.Small.Defs
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.CompactProjectionExchange
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryAffineCounitTensorNormalization
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartSingleUnitor
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor

/-! # Projection and ordered affine counit on a Cartesian chart

Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, simultaneous trivializations and ordered affine counits.
(blueprint: lem-pur-vector-integration-cartesian-projection-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] rightDerivedLowerShriek upperStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme leftDerivedUpperStarComp
  leftDerivedUpperStarIsoMapDerivedCategory
attribute [local implicit_reducible] Scheme.Modules

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem projection_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {W W' : DerivedCategoryModule A X} (c : W ⟶ W')
    (K : DerivedCategoryModule A Y) :
    ((ordinaryFiniteTensor A Y).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map c) ≫
      compactSupportProjectionMap A f W' K =
    compactSupportProjectionMap A f W K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((ordinaryFiniteTensor A X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).map c) := by
  rw [compactSupportProjectionMap_eq, compactSupportProjectionMap_eq]
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let Q := ordinaryFinitePullback A f
  let U := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let T := derivedTensor (ModuleCat.{u + 1} A) X
  have hs := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).naturality
    (F.map c)
  have hp := NatTrans.naturality_app
    (projectionMap (ModuleCat.{u + 1} A) f) K c
  have he := ((T.map c).naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)).symm
  have ht := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
    (U.obj K)).naturality c
  change ((ordinaryFiniteTensor A Y).obj K).map (F.map c) ≫
      (_ ≫ ((projectionMap (ModuleCat.{u + 1} A) f).app W').app K ≫
        F.map ((T.obj W').map _) ≫ F.map _) =
    (_ ≫ ((projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
        F.map ((T.obj W).map _) ≫ F.map _) ≫ F.map _
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app] at hs ht
  change ((T.map c).app (Q.obj K)) ≫ (T.obj W').map _ =
    (T.obj W).map _ ≫ (T.map c).app (U.obj K) at he
  change ((derivedTensor (ModuleCat.{u + 1} A) Y).map (F.map c)).app K ≫
      ((projectionMap (ModuleCat.{u + 1} A) f).app W').app K =
    ((projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
      F.map ((T.map c).app (Q.obj K)) at hp
  exact projection_paste F _ _ _ _ _ _ _ _ _ _ _ _ _ hs hp he ht

private theorem tower_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T] (d : ℕ) :
    affineDualizingTowerComparison A T d = affineTraceUnboundedCompactComparison A T d := by
  delta affineDualizingTowerComparison affineTraceUnboundedCompactComparison
  rfl

private theorem descent_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (K : DerivedCategoryModule A T) :
    OrdinaryAffineCounitTensorNormalization.descent A N hA t T hT d K =
      VectorIntegrationDirectSumCounit.coefficientDescent A N hA t T hT d K := by
  unfold OrdinaryAffineCounitTensorNormalization.descent
    VectorIntegrationDirectSumCounit.coefficientDescent
    OrdinaryAffineCounitTensorNormalization.descentStep
    VectorIntegrationDirectSumCounit.coefficientDescentStep
  rfl

private theorem unit_comparison_eq
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    affineLinearCompactComparison N hN A hA S hS d =
      (affineTraceUnboundedCompactComparison A S d).app
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) := by
  let K : DerivedCategory.Plus
      (Sheaf (affineTraceTower S d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S),
      Exists.elim (exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 S hS d).2.1))⟩
  apply Iso.ext
  change (affineTracePlusCompatibility A S d).inv.app K ≫
    DerivedCategory.Plus.ι.map ((affineTraceCompactSupportComparison A S d).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
        (affineTraceProjection S d)).hom.app K =
    (affineTraceUnboundedCompactComparison A S d).hom.app (DerivedCategory.Plus.ι.obj K)
  apply (cancel_epi ((affineTracePlusCompatibility A S d).hom.app K)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (affineTraceUnboundedCompactComparison_restriction A S d K).symm

private theorem canonical_sym_swap
    (C : Type*) [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [HasDerivedCategory.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      ((_root_.DerivedCategory.canonicalTensorSymmetry C).inv.app M).app K := by
  let := _root_.DerivedCategory.symmetricCategory' C
  exact SymmetricCategory.braiding_swap_eq_inv_braiding M K

private theorem projection_coeffFirst
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (p : X ⟶ S) [HasCompactification p]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A S) :
    compactSupportProjectionMap A p M K = compactProjectionMapCoeffFirst A p K M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
        (((ordinaryFiniteTensor A X).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).app K).hom).app
            M) := by
  have hs : ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).app
      ((ordinaryFinitePullback A p).obj K) =
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
      ((ordinaryFinitePullback A p).obj K)).app M := by
    unfold derivedTensorSymmetry
    exact canonical_sym_swap (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      M ((ordinaryFinitePullback A p).obj K)
  have hn := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).app K).hom) M
  change _ ≫ _ = _ ≫ _ at hn
  rw [compactSupportProjectionMap_eq, compactProjectionMapCoeffFirst]
  dsimp only [ordinaryFinitePullback, ordinaryFiniteTensor] at hs ⊢
  rw [hs]
  simpa only [Functor.map_comp, Functor.flip_map_app, Iso.app_hom, Category.assoc] using congrArg
    (fun z ↦ ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app K).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M) ≫
      ((projectionMap (ModuleCat.{u + 1} A) p).app M).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map z) hn

private theorem tensor_map_iso
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    ordinaryFiniteTensorRightMapIso A T e c = tensorIso e c := by
  apply Iso.ext
  rfl

private def affine_tensor_descent
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (K : DerivedCategoryModule A T) :
    (affineTraceRight A N hA T d).obj K ≅
      ((ordinaryFiniteTensor A (affineTraceTower T d)).obj
        ((upperStar (ModuleCat.{u + 1} A) (affineTraceProjection T d)).mapDerivedCategory.obj
          K)).obj
        ((ordinaryFinitePullback A (affineTraceProjection T d)).obj
          (affineLinearBaseCoefficient A N hA T d)) :=
  VectorIntegrationDirectSumCounit.coefficientDescent A N hA t T hT d K ≪≫
    ordinaryFiniteTensorPullback A (affineTraceProjection T d) K
      (affineLinearBaseCoefficient A N hA T d) ≪≫
    ordinaryFiniteTensorRightMapIso A (affineTraceTower T d)
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (affineTraceProjection T d)).app K) (Iso.refl _)

private theorem affine_tensor_normalization
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))
    (d : ℕ) (K : DerivedCategoryModule A T) :
    compactSupportProjectionMap A (affineTraceProjection T d)
        ((ordinaryFinitePullback A (affineTraceProjection T d)).obj
          (affineLinearBaseCoefficient A N hA T d)) K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
        (affine_tensor_descent A N hA t T hT d K).inv ≫
      (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
      (affineTraceAdjunction A N hA t D T hT d).counit.app K =
    ((ordinaryFiniteTensor A T).obj K).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
          (affineLinearCoefficientDescent A N hA t T hT d).inv ≫
        (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
        affineTraceCounit A N hA t D T hT d) ≫ (derivedTensorSingleUnitIso K).hom := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)
  let W := (ordinaryFinitePullback A (affineTraceProjection T d)).obj
    (affineLinearBaseCoefficient A N hA T d)
  let V := SectionLocalDualizingComparisons.tateObject A N hA (affineTraceTower T d) d
  let TC := (ordinaryFiniteTensor A (affineTraceTower T d)).obj
    ((upperStar (ModuleCat.{u + 1} A) (affineTraceProjection T d)).mapDerivedCategory.obj K)
  let TD := (ordinaryFiniteTensor A T).obj K
  let c : W ≅ V := (affineLinearCoefficientDescent A N hA t T hT d).symm ≪≫
    CoordinateCounitArrows.towerTateIso A N hN hA t T hT d
  let eV := OrdinaryAffineCounitTensorNormalization.reassociation A N hN hA t T hT d K
  let z := (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
    (affineTraceAdjunction A N hA t D T hT d).counit.app K
  let tr := F.map (affineLinearCoefficientDescent A N hA t T hT d).inv ≫
    (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
    affineTraceCounit A N hA t D T hT d
  have he : eV = affine_tensor_descent A N hA t T hT d K ≪≫ TC.mapIso c := by
    apply Iso.ext
    simp only [eV, OrdinaryAffineCounitTensorNormalization.reassociation, descent_eq,
      affine_tensor_descent, tensor_map_iso, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, Functor.mapIso_hom, c, TC, ordinaryFiniteTensor,
      derivedTensor_obj_map, MonoidalCategory.tensorHom_def, whiskerLeft_id,
      Category.comp_id, Category.assoc]
  have hz : OrdinaryAffineCounitTensorNormalization.counit A N hN hA t D T hT d K =
      F.map eV.inv ≫ z := by
    simp only [OrdinaryAffineCounitTensorNormalization.counit, tower_comparison_eq]
    rfl
  have ht : OrdinaryAffineCounitTensorNormalization.trace A N hN hA t D T hT d =
      F.map c.inv ≫ tr := by
    simp only [OrdinaryAffineCounitTensorNormalization.trace, tower_comparison_eq,
      c, tr, Iso.trans_inv, Iso.symm_inv, Functor.map_comp, Category.assoc]
    simp only [F, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      Category.comp_id]
  obtain ⟨P, hP, hn⟩ := ordinaryAffineCounit_tensor_normalization N hN A hA t D T hT d K
  have hn' : compactSupportProjectionMap A (affineTraceProjection T d) V K ≫
      F.map eV.inv ≫ z =
    TD.map (OrdinaryAffineCounitTensorNormalization.trace A N hN hA t D T hT d) ≫
      (derivedTensorSingleUnitIso K).hom := by
    rw [← hz, ← hP, hn, Iso.hom_inv_id_assoc]
    rfl
  exact normalization_transport F TC TD
    (fun M ↦ compactSupportProjectionMap A (affineTraceProjection T d) M K)
    (fun m ↦ projection_naturality A (affineTraceProjection T d) m K)
    c (affine_tensor_descent A N hA t T hT d K) eV he z tr _ ht
    (derivedTensorSingleUnitIso K).hom hn'

private theorem tensor_pullback_eq
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategoryModule A Y) :
    ordinaryFiniteTensorPullback A f K M =
      leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K M := by
  rfl

private theorem coefficient_projection_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (K : DerivedCategoryModule A S) {C D : DerivedCategoryModule A X} (φ : C ⟶ D) :
    ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map φ) ≫
      compactProjectionMapCoeffFirst A f K D =
    compactProjectionMapCoeffFirst A f K C ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((ordinaryFinitePullback A f).obj K)).map φ) := by
  have hp : ((derivedTensor (ModuleCat.{u + 1} A) S).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map φ)).app K ≫
      ((projectionMap (ModuleCat.{u + 1} A) f).app D).app K =
    ((projectionMap (ModuleCat.{u + 1} A) f).app C).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map φ).app
          ((ordinaryFinitePullback A f).obj K)) := by
    exact NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} A) f).naturality φ) K
  have hτ := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app K).naturality
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map φ)
  have hσ := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).congr_map
    (NatTrans.congr_app
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.naturality φ)
      ((ordinaryFinitePullback A f).obj K))
  simp only [NatTrans.comp_app, Functor.map_comp] at hσ
  dsimp only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map, Functor.flip_obj_map, Functor.whiskeringLeft_obj_obj,
    Functor.whiskeringRight_obj_obj] at hp
  simpa only [compactProjectionMapCoeffFirst, Functor.flip_map_app,
    Functor.flip_obj_obj, Functor.flip_obj_map, ordinaryFinitePullback,
    Category.assoc] using
    three_squares _ _ _ _ _ _ _ _ _ _ hτ hp hσ

private theorem coefficient_projection_left
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (p : X ⟶ S) [HasCompactification p]
    (M : DerivedCategoryModule A X) {K K' : DerivedCategoryModule A S} (k : K ⟶ K') :
    ((ordinaryFiniteTensor A S).map k).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M) ≫
      compactProjectionMapCoeffFirst A p K' M =
    compactProjectionMapCoeffFirst A p K M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
        (((ordinaryFiniteTensor A X).map ((ordinaryFinitePullback A p).map k)).app M) := by
  have hp := ((projectionMap (ModuleCat.{u + 1} A) p).app M).naturality k
  have hτ := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.naturality k)
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M)
  have hσ := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).congr_map
    (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).naturality
      ((ordinaryFinitePullback A p).map k))
  simp only [Functor.map_comp] at hσ
  dsimp only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map, Functor.flip_obj_map, Functor.whiskeringLeft_obj_obj,
    Functor.whiskeringRight_obj_obj] at hp
  simpa only [compactProjectionMapCoeffFirst, Functor.flip_map_app,
    Functor.flip_obj_obj, Functor.flip_obj_map, ordinaryFinitePullback, ordinaryFiniteTensor,
    Category.assoc] using
    three_squares _ _ _ _ _ _ _ _ _ _ hτ hp hσ

private theorem coefficient_projection_both
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (p : X ⟶ S) [HasCompactification p]
    {M M' : DerivedCategoryModule A X} {K K' : DerivedCategoryModule A S}
    (k : K ⟶ K') (m : M ⟶ M') :
    compactProjectionMapCoeffFirst A p K M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map
        ((ordinaryFinitePullback A p).map k ⊗ₘ m) =
    (k ⊗ₘ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).map m) ≫
      compactProjectionMapCoeffFirst A p K' M' := by
  have hk := coefficient_projection_left A p M k
  have hm := coefficient_projection_naturality A p K' m
  simp only [ordinaryFiniteTensor, derivedTensor_map_app, derivedTensor_obj_map] at hk hm
  simp only [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hk, ← hm]

private def cartesian_tensor
    (A : Type (u + 1)) [CommRing A]
    {X S Y T : Scheme.{u}} (p : X ⟶ S) (a : Y ⟶ T) (f : T ⟶ S) (q : Y ⟶ X)
    (sq : IsPullback q a p f) (M : DerivedCategoryModule A X)
    (M' : DerivedCategoryModule A Y) (K : DerivedCategoryModule A S)
    (K' : DerivedCategoryModule A T) (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (cM : (ordinaryFinitePullback A q).obj M ≅ M') :
    (ordinaryFinitePullback A q).obj
      (((ordinaryFiniteTensor A X).obj
        ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K)).obj M) ≅
    ((ordinaryFiniteTensor A Y).obj
      ((upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategory.obj K')).obj M' :=
  ordinaryFiniteTensorPullback A q
      ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K) M ≪≫
    ordinaryFiniteTensorRightMapIso A Y
      ((ordinaryFinitePullback A q).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).app K).symm ≪≫
        (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K ≪≫
        (ordinaryFinitePullback A a).mapIso cK ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).app K') cM

private theorem cartesian_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S Y T : Scheme.{u}} (p : X ⟶ S) (a : Y ⟶ T) (f : T ⟶ S) (q : Y ⟶ X)
    [HasCompactification p] [HasCompactification a] [QuasiCompact a]
    (sq : IsPullback q a p f) (M : DerivedCategoryModule A X)
    (M' : DerivedCategoryModule A Y) (K : DerivedCategoryModule A S)
    (K' : DerivedCategoryModule A T) (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (cM : (ordinaryFinitePullback A q).obj M ≅ M') :
    (ordinaryFinitePullback A f).map (compactSupportProjectionMap A p M K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).map
        (cartesian_tensor A p a f q sq M M' K K' cK cM).hom =
    (ordinaryFiniteTensorPullback A f K
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M)).hom ≫
      (cK.hom ⊗ₘ ((rightDerivedLowerShriekBaseChangeMap A sq).app M ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).map cM.hom)) ≫
      compactSupportProjectionMap A a M' K' := by
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) a
  let Q := ordinaryFinitePullback A q
  let B := ordinaryFinitePullback A f
  let E := rightDerivedLowerShriekBaseChangeMap A sq
  let l := ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).app K)
  let l' := ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).app K')
  let v := (ordinaryFiniteTensorPullback A q ((ordinaryFinitePullback A p).obj K) M).hom ≫
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv.app K ⊗ₘ
      𝟙 (Q.obj M))
  let w := ((ordinaryFinitePullback A a).map cK.hom ⊗ₘ cM.hom)
  have hu : Q.map (l.hom ⊗ₘ 𝟙 M) ≫
      (cartesian_tensor A p a f q sq M M' K K' cK cM).hom =
    v ≫ w ≫ (l'.hom ⊗ₘ 𝟙 M') := by
    have hn : Q.map (l.hom ⊗ₘ 𝟙 M) ≫
        (ordinaryFiniteTensorPullback A q
          ((upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory.obj K) M).hom =
      (ordinaryFiniteTensorPullback A q ((ordinaryFinitePullback A p).obj K) M).hom ≫
        (Q.map l.hom ⊗ₘ 𝟙 (Q.obj M)) := by
      simpa only [Q, ordinaryFinitePullback, tensor_pullback_eq,
        tensorHom_id, derivedTensor_map_app] using
        leftDerivedUpperStarTensorIso_hom_naturality_left q l.hom M
    simp only [cartesian_tensor, tensor_map_iso, Iso.trans_hom, tensorIso_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
    rw [reassoc_of% hn]
    simp only [v, w, l, l', Iso.app_hom,
      Category.assoc,
      tensorHom_comp_tensorHom, Category.comp_id]
    simp only [Q, Iso.app_inv, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Category.id_comp]
    simp only [ordinaryFinitePullback, CategoryTheory.Functor.map_id, Category.id_comp]
  have hp := compactProjectionMapCoeffFirst_baseChangeMap A sq M K
  have hv : B.map (compactProjectionMapCoeffFirst A p K M) ≫
      E.app _ ≫ R.map v =
    (ordinaryFiniteTensorPullback A f K
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj M)).hom ≫
      (𝟙 (B.obj K) ⊗ₘ E.app M) ≫
      compactProjectionMapCoeffFirst A a (B.obj K) (Q.obj M) := by
    simpa only [v, R, B, Q, E, Functor.map_comp, Category.assoc, tensorHom_id,
      id_tensorHom, tensor_pullback_eq, ordinaryFinitePullback,
      leftDerivedUpperStarTensorIso_hom,
      derivedTensor_map_app, derivedTensor_obj_map, derivedSquareUpperStarIsoInvApp] using hp
  dsimp only [Q, ordinaryFinitePullback, l] at hu
  dsimp only [B, Q, E, R, ordinaryFinitePullback] at hv
  have hw := coefficient_projection_both A a cK.hom cM.hom
  dsimp only [ordinaryFinitePullback] at hw
  have ha := projection_coeffFirst A a M' K'
  simp only [ordinaryFiniteTensor, derivedTensor_map_app, ← tensorHom_id] at ha
  have hn := E.naturality (((ordinaryFiniteTensor A X).map l.hom).app M)
  dsimp only [Functor.comp_map] at hn
  dsimp only [ordinaryFinitePullback, ordinaryFiniteTensor, l, E] at hn
  rw [projection_coeffFirst, Functor.map_comp]
  simp only [Category.assoc]
  dsimp only [ordinaryFinitePullback, ordinaryFiniteTensor]
  rw [reassoc_of% hn]
  simp only [derivedTensor_map_app, ← tensorHom_id]
  rw [← Functor.map_comp, hu]
  simp only [Functor.map_comp]
  rw [reassoc_of% hv]
  dsimp only [w, l', ordinaryFinitePullback]
  rw [reassoc_of% hw, ← ha]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]

private theorem cartesian_descent_factor
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X S T : Scheme.{u}} (p : X ⟶ S) (f : T ⟶ S)
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L K : DerivedCategoryModule A S) (K' : DerivedCategoryModule A T)
    (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    vectorIntegrationCartesianTensorDescent A N hA t p f hT d q sq L K K' cK b =
      affine_tensor_descent A N hA t T hT d K' ≪≫
        (cartesian_tensor A p (affineTraceProjection T d) f q sq
          ((ordinaryFinitePullback A p).obj L)
          ((ordinaryFinitePullback A (affineTraceProjection T d)).obj
            (affineLinearBaseCoefficient A N hA T d)) K K' cK
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app L ≪≫
            (ordinaryFinitePullback A (affineTraceProjection T d)).mapIso b)).symm := by
  apply Iso.ext
  simp only [vectorIntegrationCartesianTensorDescent, affine_tensor_descent,
    cartesian_tensor, tensor_map_iso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, tensorIso_hom, tensorIso_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.refl_hom, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app_assoc, Category.id_comp]

private theorem single_unitor_naturality
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' : DerivedCategoryModule A T} (k : K ⟶ K') :
    ((ordinaryFiniteTensor A T).map k).app (ordinaryFiniteUnit A T) ≫
      (derivedTensorSingleUnitIso K').hom =
    (derivedTensorSingleUnitIso K).hom ≫ k := by
  rw [ordinaryChartSingleUnitor_eq T K', ordinaryChartSingleUnitor_eq T K]
  have h := ((ordinaryFiniteTensor A T).map k).naturality
    (ordinaryFiniteSingleUnitIso A T).hom
  have h' := (derivedTensorRightUnitorNatIso (ModuleCat.{u + 1} A) T).hom.naturality k
  dsimp only [derivedTensorRightUnitorNatIso, NatIso.ofComponents,
    Functor.flip_obj_map, Functor.id_map] at h'
  rw [← reassoc_of% h]
  simpa only [ordinaryFiniteTensor, Category.assoc] using
    congrArg
      (((ordinaryFiniteTensor A T).obj K).map (ordinaryFiniteSingleUnitIso A T).hom ≫ ·) h'

private theorem tensor_trace_naturality
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' M J : DerivedCategoryModule A T} (k : K ⟶ K')
    (m : M ⟶ J) (tr : J ⟶ ordinaryFiniteUnit A T) :
    (k ⊗ₘ m) ≫ ((ordinaryFiniteTensor A T).obj K').map tr ≫
      (derivedTensorSingleUnitIso K').hom =
    ((ordinaryFiniteTensor A T).obj K).map (m ≫ tr) ≫
      (derivedTensorSingleUnitIso K).hom ≫ k := by
  have hn := ((ordinaryFiniteTensor A T).map k).naturality (m ≫ tr)
  simp only [ordinaryFiniteTensor, derivedTensor_map_app, derivedTensor_obj_map,
    whiskerLeft_comp, Category.assoc] at hn
  simp only [ordinaryFiniteTensor, MonoidalCategory.tensorHom_def,
    derivedTensor_obj_map, Category.assoc]
  rw [← reassoc_of% hn]
  simpa only [ordinaryFiniteTensor, derivedTensor_obj_map, derivedTensor_map_app,
    whiskerLeft_comp,
    Category.assoc] using congrArg
      (((ordinaryFiniteTensor A T).obj K).map (m ≫ tr) ≫ ·)
      (single_unitor_naturality A T k)

/-- The Cartesian projection square followed by the ordered affine counit.
Source: vector-bundle purity proof, paragraph 2, tensor normalization of the inner block.
(blueprint: lem-pur-vector-integration-cartesian-projection-counit).

Proof:
1. Write a=affineTraceProjection T d, E for the Cartesian shriek exchange, δ for pullback tensor
comparison, S for derivedSquareUpperStarIso, and ℓ for leftDerivedUpperStarIsoMapDerivedCategory.
The inverse-image map u from q*(termwise p*K tensor p*L) to termwise a*(f*K) tensor q*p*L is δ_q
followed in its first factor by q*(ℓ_p inverse), S_K inverse and ℓ_a. Conjugate
compactProjectionMapCoeffFirst_baseChangeMap by these exact-pullback comparisons. Exchange
naturality and δ naturality cancel q*ℓ_p against q*(ℓ_p inverse), giving f*P_p followed by E and
a!u equal to δ_f, tensor of E, and P_a. No exchange map is inverted.

2. For a coefficient J on T let e0 be coefficientDescent J, then δ_a, then tensor of ℓ_a(J) and
the identity. The affine identity is P_a(a*P_d,J) followed by a!e0 inverse, C_d inverse and ε_d(J)
equal to tensor J of the unit affine trace followed by the right unitor. Derive it from
ordinaryAffineCounit_tensor_normalization: transport its Tate object by
(affineLinearCoefficientDescent inverse) followed by towerTateIso; projection naturality moves
this specified isomorphism through P_a, and the two towerTateIso factors cancel. Explicit
unfolding identifies affineDualizingTowerComparison with affineTraceUnboundedCompactComparison. At
the unit its bounded-below comparison equals C_d by the restriction theorem.

3. In the equation of step 1 transport the second factor q*p*L along S_L inverse followed by
a*(b.hom). Transport the first factor from f*K to K′ along cK. Projection naturality in both
variables moves these maps to the affine formula of step 2, after factoring the specified
Cartesian tensor descent as the affine descent followed by the inverse Cartesian comparison.
Expanding the constructed tensor descent shows that these are exactly its factors, with no
unspecified comparison isomorphism.

4. The unit trace after these transports is E at p*L, then a! of S_L inverse, a!(a*b), inverse
affine coefficient descent, C_d inverse at the unit, and ε_d at the unit. These are precisely
vectorIntegrationCartesianPrefix followed by affineTraceCounit. Tensor pullback and right-unitor
naturality give the displayed right side ending in cK.hom. The d=0 formulas use the identity
adjunction and tensor unit; no step needs a nonempty base or a nonzero ring. The existing
ordinaryChartSingleUnitor_eq supplies the single-unit endpoints for right-unitor naturality.
-/
theorem vectorIntegrationCartesianProjectionCounit
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S T : Scheme.{u}} [IsNoetherian T]
    (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L K : DerivedCategoryModule A S) (K' : DerivedCategoryModule A T)
    (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (ordinaryFinitePullback A f).map
        (compactSupportProjectionMap A p ((ordinaryFinitePullback A p).obj L) K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
        (vectorIntegrationCartesianTensorDescent A N hA t p f hT d q sq L K K' cK b).inv ≫
      (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
      (affineTraceAdjunction A N hA t D T hT d).counit.app K' =
    (ordinaryFiniteTensorPullback A f K
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj
        ((ordinaryFinitePullback A p).obj L))).hom ≫
      ((ordinaryFiniteTensor A T).obj ((ordinaryFinitePullback A f).obj K)).map
        (vectorIntegrationCartesianPrefix N hN A hA t p f hT d q sq L b ≫
          affineTraceCounit A N hA t D T hT d) ≫
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).hom ≫ cK.hom := by
  let a := affineTraceProjection T d
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) a
  let M := (ordinaryFinitePullback A p).obj L
  let M' := (ordinaryFinitePullback A a).obj (affineLinearBaseCoefficient A N hA T d)
  let cM : (ordinaryFinitePullback A q).obj M ≅ M' :=
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app L ≪≫
      (ordinaryFinitePullback A a).mapIso b
  let m := (rightDerivedLowerShriekBaseChangeMap A sq).app M ≫ R.map cM.hom
  let tr := R.map (affineLinearCoefficientDescent A N hA t T hT d).inv ≫
    (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
    affineTraceCounit A N hA t D T hT d
  have ht : m ≫ tr =
      vectorIntegrationCartesianPrefix N hN A hA t p f hT d q sq L b ≫
        affineTraceCounit A N hA t D T hT d := by
    simp only [m, tr, cM, vectorIntegrationCartesianPrefix,
      vectorIntegrationCartesianCoefficient, unit_comparison_eq,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    rfl
  have hp := cartesian_projection A p a f q sq M M' K K' cK cM
  have ha := affine_tensor_normalization N hN A hA t D T hT d K'
  rw [cartesian_descent_factor]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hp, ha]
  rw [tensor_trace_naturality A T cK.hom m tr, ht]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
