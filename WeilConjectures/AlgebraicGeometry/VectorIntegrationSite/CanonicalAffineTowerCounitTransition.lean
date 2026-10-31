/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.IntegrationProjectiveExponentSquare
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ShiftedExponentTransitionPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Canonical ordered affine tower counit transition

The root transition of the ordered affine counit for the canonical twist transports and
projective-line data, by induction along the ordered coordinate tower. The line step is
proved for arbitrary complexes from the forward projective decomposition square.
Source: blueprint thm-amb-vector-bundle-purity, proof, paragraph 2 (ordered affine tower);
Stacks Tags 03PK, 03Q1.
(blueprint: lem-pur-canonical-affine-tower-counit-transition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
open MonoidalCategory Etale
attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.affineLinearBaseCoefficient Etale.derivedTensorRight

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

private noncomputable abbrev derivedBraiding (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) :
    BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :=
  _root_.DerivedCategory.braidedCategory' _
section ProjectionNaturality
attribute [local instance] derivedBraiding
attribute [local instance 2000] Abelian.toPreadditive

private theorem projection_coefficient_naturality
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (q : X ⟶ Y)
    {W V : Etale.DerivedCategoryModule A X} (f : W ⟶ V)
    (K : Etale.DerivedCategoryModule A Y) :
    Etale.ordinaryFiniteProjection A q W K ≫
      (Etale.ordinaryFinitePushforward A q).map
        (((Etale.ordinaryFinitePullback A q).obj K) ◁ f) =
    K ◁ (Etale.ordinaryFinitePushforward A q).map f ≫
      Etale.ordinaryFiniteProjection A q V K := by
  let Q := Etale.ordinaryFinitePushforward A q
  let L := Etale.ordinaryFinitePullback A q
  have hn := NatTrans.congr_app
    ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).naturality f) K
  change Q.map f ▷ K ≫
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app V).app K =
    ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app W).app K ≫
      Q.map (f ▷ L.obj K) at hn
  simp -implicitDefEqProofs only [Etale.ordinaryFiniteProjection, Category.assoc]
  change (β_ K (Q.obj W)).hom ≫
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app W).app K ≫
      Q.map (β_ W (L.obj K)).hom ≫ Q.map ((L.obj K) ◁ f) =
    K ◁ Q.map f ≫ (β_ K (Q.obj V)).hom ≫
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app V).app K ≫
      Q.map (β_ V (L.obj K)).hom
  rw [← Q.map_comp, ← BraidedCategory.braiding_naturality_left f (L.obj K),
    Q.map_comp]
  rw [← reassoc_of% hn, ← BraidedCategory.braiding_naturality_right_assoc K (Q.map f)]

end ProjectionNaturality

private theorem tensor_iso_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : Etale.DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    (Etale.ordinaryFiniteTensorRightMapIso A T e c).hom = e.hom ⊗ₘ c.hom := by
  change e.hom ▷ L ≫ K' ◁ c.hom = e.hom ⊗ₘ c.hom
  rw [MonoidalCategory.tensorHom_def]

private lemma line_descent_hom (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (K : DerivedCategoryModule A T) :
    (affineLinearLineDescent A N hA t T hT K).hom =
      (ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart T)
        ((ordinaryFinitePullback A (ProjectiveLine T ↘ T)).obj K)
        ((ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)).hom ≫
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart T) (ProjectiveLine T ↘ T)
        (AffineSpace PUnit.{u + 1} T ↘ T)
        (ProjectiveLine.affineChart_over T).symm).inv.app K ⊗ₘ
        ((ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine.affineChart T)
          (affineTraceProjectiveInvertible N T hT)).hom ≫
          (ordinaryFiniteShiftedLinePullback A N hA t
            (AffineSpace PUnit.{u + 1} T ↘ T) hT).inv)) ≫
      (ordinaryFiniteTensorPullback A (AffineSpace PUnit.{u + 1} T ↘ T) K
        ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)).inv := by
  simp only [affineLinearLineDescent, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    tensor_iso_hom]

private lemma tower_descent_step_hom (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (e : (affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePullback A (affineTraceProjection S d)).obj
        (affineLinearBaseCoefficient A N hA S d)) :
    (affineLinearCoefficientDescentStep A N hA t S hS d e).hom =
      (affineLinearLineDescent A N hA t (affineTraceTower S d)
        (affineTraceInvertible N S hS d)
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))).hom ≫
      (ordinaryFinitePullback A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).map
        ((e.hom ⊗ₘ
          (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).inv) ≫
        (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
          (affineLinearBaseCoefficient A N hA S d)
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).inv) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)).inv.app (affineLinearBaseCoefficient A N hA S (d + 1)) := by
  simp only [affineLinearCoefficientDescentStep, Iso.trans_hom, Functor.mapIso_hom,
    tensor_iso_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp]

private lemma tower_descent_succ_hom (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (affineLinearCoefficientDescent A N hA t S hS (d + 1)).hom =
      (affineLinearLineDescent A N hA t (affineTraceTower S d)
        (affineTraceInvertible N S hS d)
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))).hom ≫
      (ordinaryFinitePullback A
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)).map
        (((affineLinearCoefficientDescent A N hA t S hS d).hom ⊗ₘ
          (ordinaryFiniteShiftedLinePullback A N hA t (affineTraceProjection S d) hS).inv) ≫
        (ordinaryFiniteTensorPullback A (affineTraceProjection S d)
          (affineLinearBaseCoefficient A N hA S d)
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).inv) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d)
        (affineTraceProjection S d)).inv.app (affineLinearBaseCoefficient A N hA S (d + 1)) := by
  exact tower_descent_step_hom A N hA t S hS d
    (affineLinearCoefficientDescent A N hA t S hS d)

private theorem descent_tensor_square
    {C D B : Type*} [Category C] [Category D] [Category B]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory B]
    (Q : C ⥤ D) (J : D ⥤ B) (P : C ⥤ B) (a : Q ⋙ J ≅ P)
    {K K' Ls Lr : C} {Vs Vr : D} (f : K ⟶ K') (c : Ls ⟶ Lr) (v : Vs ⟶ Vr)
    (es : J.obj Vs ≅ P.obj Ls) (er : J.obj Vr ≅ P.obj Lr)
    (δJs : J.obj (Q.obj K ⊗ Vs) ≅ J.obj (Q.obj K) ⊗ J.obj Vs)
    (δJr : J.obj (Q.obj K' ⊗ Vr) ≅ J.obj (Q.obj K') ⊗ J.obj Vr)
    (δPs : P.obj (K ⊗ Ls) ≅ P.obj K ⊗ P.obj Ls)
    (δPr : P.obj (K' ⊗ Lr) ≅ P.obj K' ⊗ P.obj Lr)
    (hv : J.map v ≫ er.hom = es.hom ≫ P.map c)
    (hJ : δJs.hom ≫ (J.map (Q.map f) ⊗ₘ J.map v) =
      J.map (Q.map f ⊗ₘ v) ≫ δJr.hom)
    (hP : δPs.hom ≫ (P.map f ⊗ₘ P.map c) = P.map (f ⊗ₘ c) ≫ δPr.hom) :
    J.map (Q.map f ⊗ₘ v) ≫ δJr.hom ≫ (a.hom.app K' ⊗ₘ er.hom) ≫ δPr.inv =
      δJs.hom ≫ (a.hom.app K ⊗ₘ es.hom) ≫ δPs.inv ≫ P.map (f ⊗ₘ c) := by
  have hn := a.hom.naturality f
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hJ, tensorHom_comp_tensorHom_assoc, hn, hv,
    ← tensorHom_comp_tensorHom_assoc]
  have hp : (P.map f ⊗ₘ P.map c) ≫ δPr.inv = δPs.inv ≫ P.map (f ⊗ₘ c) := by
    apply (cancel_epi δPs.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using congrArg (fun g ↦ g ≫ δPr.inv) hP
  rw [hp]

private theorem descent_tensor_square_of_formula
    {C D B : Type*} [Category C] [Category D] [Category B]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory B]
    (Q : C ⥤ D) (J : D ⥤ B) (P : C ⥤ B) (a : Q ⋙ J ≅ P)
    {K K' Ls Lr : C} {Vs Vr : D} (f : K ⟶ K') (c : Ls ⟶ Lr) (v : Vs ⟶ Vr)
    (es : J.obj Vs ≅ P.obj Ls) (er : J.obj Vr ≅ P.obj Lr)
    (δJs : J.obj (Q.obj K ⊗ Vs) ≅ J.obj (Q.obj K) ⊗ J.obj Vs)
    (δJr : J.obj (Q.obj K' ⊗ Vr) ≅ J.obj (Q.obj K') ⊗ J.obj Vr)
    (δPs : P.obj (K ⊗ Ls) ≅ P.obj K ⊗ P.obj Ls)
    (δPr : P.obj (K' ⊗ Lr) ≅ P.obj K' ⊗ P.obj Lr)
    (ds : J.obj (Q.obj K ⊗ Vs) ⟶ P.obj (K ⊗ Ls))
    (dr : J.obj (Q.obj K' ⊗ Vr) ⟶ P.obj (K' ⊗ Lr))
    (hds : ds = δJs.hom ≫ (a.hom.app K ⊗ₘ es.hom) ≫ δPs.inv)
    (hdr : dr = δJr.hom ≫ (a.hom.app K' ⊗ₘ er.hom) ≫ δPr.inv)
    (hv : J.map v ≫ er.hom = es.hom ≫ P.map c)
    (hJ : δJs.hom ≫ (J.map (Q.map f) ⊗ₘ J.map v) =
      J.map (Q.map f ⊗ₘ v) ≫ δJr.hom)
    (hP : δPs.hom ≫ (P.map f ⊗ₘ P.map c) = P.map (f ⊗ₘ c) ≫ δPr.hom) :
    J.map (Q.map f ⊗ₘ v) ≫ dr = ds ≫ P.map (f ⊗ₘ c) := by
  rw [hdr, hds]
  simpa only [Category.assoc] using
    descent_tensor_square Q J P a f c v es er δJs δJr δPs δPr hv hJ hP

private theorem tower_counit_succ (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))),
      OrdinaryFiniteP1Datum A N hA t Y hY)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    affineTraceCounit A N hA t D T hT (d + 1) =
      (affineTraceLeft A T d).map
        ((affineTraceLineAdjunction A N hA t (affineTraceTower T d)
          (affineTraceInvertible N T hT d)
          (@D _ (affineTraceNoetherian T d) _)).counit.app
            ((affineTraceRight A N hA T d).obj (ordinaryFiniteUnit A T))) ≫
      affineTraceCounit A N hA t D T hT d := by
  unfold affineTraceCounit affineTraceAdjunction
  exact affineTraceAdjunctionTower_counit_succ _ d _

private theorem paste_counit_transition
    {C D B : Type*} [Category C] [Category D] [Category B]
    (L : D ⥤ C) {F : B ⥤ D} {R S : D ⥤ B} (ar : F ⊣ R) (as' : F ⊣ S)
    {Xs Xr : D} {U : C} (e : S.obj Xs ⟶ R.obj Xs) (z : Xs ⟶ Xr)
    (er : L.obj Xr ⟶ U) (es : L.obj Xs ⟶ U)
    (he : F.map e ≫ ar.counit.app Xs = as'.counit.app Xs)
    (hz : L.map z ≫ er = es) :
    (F ⋙ L).map (e ≫ R.map z) ≫ (L.map (ar.counit.app Xr) ≫ er) =
      L.map (as'.counit.app Xs) ≫ es := by
  have hn := ar.counit.naturality z
  simp only [Functor.comp_map, Functor.id_map] at hn
  calc
    _ = L.map (F.map e ≫ F.map (R.map z) ≫ ar.counit.app Xr) ≫ er := by
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    _ = L.map (F.map e ≫ ar.counit.app Xs ≫ z) ≫ er := by rw [hn]
    _ = L.map (as'.counit.app Xs ≫ z) ≫ er := by rw [← Category.assoc, he]
    _ = _ := by rw [Functor.map_comp, Category.assoc, hz]

private theorem paste_inverse_square
    {C : Type*} [Category C] {Us Ur Vs Vr Ws Wr : C}
    (js : Us ≅ Vs) (jr : Ur ≅ Vr) (cs : Ws ≅ Vs) (cr : Wr ≅ Vr)
    (a : Us ⟶ Ur) (b : Ws ⟶ Wr) (c : Vs ⟶ Vr)
    (hj : a ≫ jr.hom = js.hom ≫ c) (hp : b ≫ cr.hom = cs.hom ≫ c) :
    a ≫ (jr ≪≫ cr.symm).hom = (js ≪≫ cs.symm).hom ≫ b := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hj]
  congr 1
  apply (cancel_epi cs.hom).mp
  simp only [← Category.assoc]
  rw [← hp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

set_option maxHeartbeats 400000 in
-- Keep the coefficient ring and the normalized transports abstract in this calculation.
private theorem line_descent_naturality
    (A : Type (u + 1)) [CommRing A] (Nr Ns : ℕ)
    (hr : (Nr : A) = 0) (hs : (Ns : A) = 0)
    (tr : OrdinaryFiniteTwistTransport A Nr hr)
    (ts : OrdinaryFiniteTwistTransport A Ns hs)
    (T : Scheme.{u}) (hTr : IsUnit (Nr : Γ(T, ⊤))) (hTs : IsUnit (Ns : Γ(T, ⊤)))
    (K K' : DerivedCategoryModule A T) (f : K ⟶ K')
    (cT : (ordinaryFiniteLine A Ns hs T)⟦(2 : ℤ)⟧ ⟶
      (ordinaryFiniteLine A Nr hr T)⟦(2 : ℤ)⟧)
    (cP : (ordinaryFiniteLine A Ns hs (ProjectiveLine T))⟦(2 : ℤ)⟧ ⟶
      (ordinaryFiniteLine A Nr hr (ProjectiveLine T))⟦(2 : ℤ)⟧)
    (cX : (ordinaryFiniteLine A Ns hs (AffineSpace PUnit.{u + 1} T))⟦(2 : ℤ)⟧ ⟶
      (ordinaryFiniteLine A Nr hr (AffineSpace PUnit.{u + 1} T))⟦(2 : ℤ)⟧)
    (hj : (ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map cP ≫
        (ordinaryFiniteShiftedLinePullback A Nr hr tr (ProjectiveLine.affineChart T)
          (affineTraceProjectiveInvertible Nr T hTr)).hom =
      (ordinaryFiniteShiftedLinePullback A Ns hs ts (ProjectiveLine.affineChart T)
          (affineTraceProjectiveInvertible Ns T hTs)).hom ≫ cX)
    (hp : (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).map cT ≫
        (ordinaryFiniteShiftedLinePullback A Nr hr tr
          (AffineSpace PUnit.{u + 1} T ↘ T) hTr).hom =
      (ordinaryFiniteShiftedLinePullback A Ns hs ts
          (AffineSpace PUnit.{u + 1} T ↘ T) hTs).hom ≫ cX) :
    (ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map
        ((ordinaryFinitePullback A (ProjectiveLine T ↘ T)).map f ⊗ₘ cP) ≫
      (affineLinearLineDescent A Nr hr tr T hTr K').hom =
    (affineLinearLineDescent A Ns hs ts T hTs K).hom ≫
      (ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).map (f ⊗ₘ cT) := by
  let j := ProjectiveLine.affineChart T
  let q := ProjectiveLine T ↘ T
  let p := AffineSpace PUnit.{u + 1} T ↘ T
  let cs := ordinaryFiniteShiftedLinePullback A Ns hs ts p hTs
  let cr := ordinaryFiniteShiftedLinePullback A Nr hr tr p hTr
  let js := ordinaryFiniteShiftedLinePullback A Ns hs ts j
    (affineTraceProjectiveInvertible Ns T hTs)
  let jr := ordinaryFiniteShiftedLinePullback A Nr hr tr j
    (affineTraceProjectiveInvertible Nr T hTr)
  have hj' : (ordinaryFinitePullback A j).map cP ≫ jr.hom = js.hom ≫ cX := hj
  have hp' : (ordinaryFinitePullback A p).map cT ≫ cr.hom = cs.hom ≫ cX := hp
  have hv := paste_inverse_square js jr cs cr
    ((ordinaryFinitePullback A j).map cP) ((ordinaryFinitePullback A p).map cT) cX hj' hp'
  exact descent_tensor_square_of_formula
    (ordinaryFinitePullback A q) (ordinaryFinitePullback A j) (ordinaryFinitePullback A p)
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q p
      (ProjectiveLine.affineChart_over T).symm).symm f cT cP
    (js ≪≫ cs.symm) (jr ≪≫ cr.symm)
    (ordinaryFiniteTensorPullback A j _ _) (ordinaryFiniteTensorPullback A j _ _)
    (ordinaryFiniteTensorPullback A p _ _) (ordinaryFiniteTensorPullback A p _ _)
    (affineLinearLineDescent A Ns hs ts T hTs K).hom
    (affineLinearLineDescent A Nr hr tr T hTr K').hom
    (line_descent_hom A Ns hs ts T hTs K) (line_descent_hom A Nr hr tr T hTr K') hv
    (Etale.leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) j _ _)
    (Etale.leftDerivedUpperStarTensorComparison_naturality (ModuleCat.{u + 1} A) p _ _)

private theorem conjugated_iso_right
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {Bs Br : C} {Ks Kr : D} (es : Ks ≅ P.obj Bs) (er : Kr ≅ P.obj Br)
    (b : Bs ≅ Br) :
    (es ≪≫ P.mapIso b ≪≫ er.symm).hom ≫ er.hom = es.hom ≫ P.map b.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverse_pullback_square
    {C : Type*} [Category C] {U V U' V' : C}
    (cs : U ≅ U') (cr : V ≅ V') (f : U ⟶ V) (g : U' ⟶ V')
    (h : f ≫ cr.hom = cs.hom ≫ g) : g ≫ cr.inv = cs.inv ≫ f := by
  apply (cancel_epi cs.hom).mp
  simp only [← Category.assoc]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

private theorem map_tensor_whiskers
    {C D B : Type*} [Category C] [Category D] [Category B] [MonoidalCategory D]
    (Q : C ⥤ D) (J : D ⥤ B) {Ks Kr : C} {Ls Lr : D}
    (f : Ks ⟶ Kr) (v : Ls ⟶ Lr) :
    J.map (Q.obj Ks ◁ v) ≫ J.map (Q.map f ▷ Lr) = J.map (Q.map f ⊗ₘ v) := by
  rw [← Functor.map_comp, ← tensorHom_def']

private theorem inverse_tensor_descent_square
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (P : C ⥤ D) {Bs Br Ls Lr : C} {Ks Kr Vs Vr : D}
    (es : Ks ≅ P.obj Bs) (er : Kr ≅ P.obj Br)
    (cs : P.obj Ls ≅ Vs) (cr : P.obj Lr ≅ Vr)
    (δs : P.obj (Bs ⊗ Ls) ≅ P.obj Bs ⊗ P.obj Ls)
    (δr : P.obj (Br ⊗ Lr) ≅ P.obj Br ⊗ P.obj Lr)
    (b : Bs ⟶ Br) (c : Ls ⟶ Lr) (z : Ks ⟶ Kr) (v : Vs ⟶ Vr)
    (hz : z ≫ er.hom = es.hom ≫ P.map b)
    (hc : v ≫ cr.inv = cs.inv ≫ P.map c)
    (hn : δs.hom ≫ (P.map b ⊗ₘ P.map c) = P.map (b ⊗ₘ c) ≫ δr.hom) :
    (z ⊗ₘ v) ≫ ((er.hom ⊗ₘ cr.inv) ≫ δr.inv) =
      ((es.hom ⊗ₘ cs.inv) ≫ δs.inv) ≫ P.map (b ⊗ₘ c) := by
  have hp : (P.map b ⊗ₘ P.map c) ≫ δr.inv = δs.inv ≫ P.map (b ⊗ₘ c) := by
    apply (cancel_epi δs.hom).mp
    rw [← Category.assoc, hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc, hz, hc, ← tensorHom_comp_tensorHom_assoc, hp]
  exact (Category.assoc _ _ _).symm

private theorem paste_descent_successor
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {Ks Kr Bs Br : C} {U V W Zs Zr : D}
    (e : U ⟶ V) (g : V ⟶ W) (j : U ⟶ W)
    (dr : W ⟶ Q.obj Kr) (ds : U ⟶ Q.obj Ks) (w : Ks ⟶ Kr)
    (αr : Kr ⟶ Br) (αs : Ks ⟶ Bs) (b : Bs ⟶ Br)
    (cr : Q.obj Br ⟶ Zr) (cs : Q.obj Bs ⟶ Zs) (z : Zs ⟶ Zr)
    (hr : W ⟶ Zr) (hs : U ⟶ Zs)
    (hR : hr = dr ≫ Q.map αr ≫ cr) (hS : hs = ds ≫ Q.map αs ≫ cs)
    (he : e ≫ g = j) (hl : j ≫ dr = ds ≫ Q.map w)
    (ht : w ≫ αr = αs ≫ b) (hc : Q.map b ≫ cr = cs ≫ z) :
    e ≫ g ≫ hr = hs ≫ z := by
  calc
    e ≫ g ≫ hr = ((e ≫ g) ≫ dr) ≫ Q.map αr ≫ cr := by
      rw [hR]
      simp only [Category.assoc]
    _ = (ds ≫ Q.map w) ≫ Q.map αr ≫ cr := by rw [he, hl]
    _ = ds ≫ Q.map (w ≫ αr) ≫ cr := by simp only [Functor.map_comp, Category.assoc]
    _ = ds ≫ Q.map (αs ≫ b) ≫ cr := by rw [ht]
    _ = ds ≫ Q.map αs ≫ (Q.map b ≫ cr) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ds ≫ Q.map αs ≫ (cs ≫ z) := by rw [hc]
    _ = hs ≫ z := by rw [hS]; simp only [Category.assoc]

private theorem tower_descent_successor_of_squares
    (A : Type (u + 1)) [CommRing A] (Nr Ns : ℕ)
    (hr : (Nr : A) = 0) (hs : (Ns : A) = 0)
    (tr : OrdinaryFiniteTwistTransport A Nr hr) (ts : OrdinaryFiniteTwistTransport A Ns hs)
    (T : Scheme.{u}) (hTr : IsUnit (Nr : Γ(T, ⊤)))
    (hTs : IsUnit (Ns : Γ(T, ⊤))) (d : ℕ) :
    let X := affineTraceTower T d
    let p := affineTraceProjection T d
    let q := AffineSpace PUnit.{u + 1} X ↘ X
    let Ks := (affineTraceRight A Ns hs T d).obj (ordinaryFiniteUnit A T)
    let Kr := (affineTraceRight A Nr hr T d).obj (ordinaryFiniteUnit A T)
    let Bs := affineLinearBaseCoefficient A Ns hs T d
    let Br := affineLinearBaseCoefficient A Nr hr T d
    let Ls := (ordinaryFiniteLine A Ns hs T)⟦(2 : ℤ)⟧
    let Lr := (ordinaryFiniteLine A Nr hr T)⟦(2 : ℤ)⟧
    let es := affineLinearCoefficientDescent A Ns hs
      ts T
      hTs d
    let er := affineLinearCoefficientDescent A Nr hr
      tr T
      hTr d
    let cs := ordinaryFiniteShiftedLinePullback A Ns hs
      ts p
      hTs
    let cr := ordinaryFiniteShiftedLinePullback A Nr hr
      tr p
      hTr
    ∀ (b : Bs ≅ Br) (c : Ls ⟶ Lr)
      (cx : ((ordinaryFiniteLine A Ns hs X)⟦(2 : ℤ)⟧) ⟶
        ((ordinaryFiniteLine A Nr hr X)⟦(2 : ℤ)⟧))
      (cp : ((ordinaryFiniteLine A Ns hs (ProjectiveLine X))⟦(2 : ℤ)⟧) ⟶
        ((ordinaryFiniteLine A Nr hr (ProjectiveLine X))⟦(2 : ℤ)⟧)),
      let z := (es ≪≫ (ordinaryFinitePullback A p).mapIso b ≪≫ er.symm).hom
      (ordinaryFinitePullback A p).map c ≫ cr.hom = cs.hom ≫ cx →
      (ordinaryFinitePullback A (ProjectiveLine.affineChart X)).map
          ((ordinaryFinitePullback A (ProjectiveLine X ↘ X)).map z ⊗ₘ cp) ≫
          (affineLinearLineDescent A Nr hr tr X (affineTraceInvertible Nr T hTr d) Kr).hom =
        (affineLinearLineDescent A Ns hs ts X (affineTraceInvertible Ns T hTs d) Ks).hom ≫
          (ordinaryFinitePullback A q).map (z ⊗ₘ cx) →
      (ordinaryFinitePullback A (ProjectiveLine.affineChart X)).map
          (((ordinaryFinitePullback A (ProjectiveLine X ↘ X)).obj Ks) ◁ cp) ≫
          (affineTraceLineRight A Nr hr X).map z ≫
          (affineLinearCoefficientDescent A Nr hr tr T hTr (d + 1)).hom =
        (affineLinearCoefficientDescent A Ns hs ts T hTs (d + 1)).hom ≫
          (ordinaryFinitePullback A (affineTraceProjection T (d + 1))).map (b.hom ⊗ₘ c) := by
  dsimp only
  intro b c cx cp hshift hline
  let X := affineTraceTower T d
  let p := affineTraceProjection T d
  let q := AffineSpace PUnit.{u + 1} X ↘ X
  let Ks := (affineTraceRight A Ns hs T d).obj (ordinaryFiniteUnit A T)
  let Kr := (affineTraceRight A Nr hr T d).obj (ordinaryFiniteUnit A T)
  let Bs := affineLinearBaseCoefficient A Ns hs T d
  let Br := affineLinearBaseCoefficient A Nr hr T d
  let Ls := (ordinaryFiniteLine A Ns hs T)⟦(2 : ℤ)⟧
  let Lr := (ordinaryFiniteLine A Nr hr T)⟦(2 : ℤ)⟧
  let es := affineLinearCoefficientDescent A Ns hs
    ts T
    hTs d
  let er := affineLinearCoefficientDescent A Nr hr
    tr T
    hTr d
  let cs := ordinaryFiniteShiftedLinePullback A Ns hs
    ts p
    hTs
  let cr := ordinaryFiniteShiftedLinePullback A Nr hr
    tr p
    hTr
  let z := (es ≪≫ (ordinaryFinitePullback A p).mapIso b ≪≫ er.symm).hom
  let αs := (es.hom ⊗ₘ cs.inv) ≫ (ordinaryFiniteTensorPullback A p Bs Ls).inv
  let αr := (er.hom ⊗ₘ cr.inv) ≫ (ordinaryFiniteTensorPullback A p Br Lr).inv
  have hz : z ≫ er.hom = es.hom ≫ (ordinaryFinitePullback A p).map b.hom := by
    exact conjugated_iso_right (ordinaryFinitePullback A p) es er b
  have hc : cx ≫ cr.inv = cs.inv ≫ (ordinaryFinitePullback A p).map c := by
    exact inverse_pullback_square cs cr ((ordinaryFinitePullback A p).map c) cx
      hshift
  have ht : (z ⊗ₘ cx) ≫ αr =
      αs ≫ (ordinaryFinitePullback A p).map (b.hom ⊗ₘ c) := by
    exact inverse_tensor_descent_square (ordinaryFinitePullback A p) es er cs cr
      (ordinaryFiniteTensorPullback A p Bs Ls) (ordinaryFiniteTensorPullback A p Br Lr)
      b.hom c z cx hz hc
      (Etale.leftDerivedUpperStarTensorComparison_naturality
        (ModuleCat.{u + 1} A) p b.hom c)
  have hm : (ordinaryFinitePullback A q).map
        ((ordinaryFinitePullback A p).map (b.hom ⊗ₘ c)) ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Br ⊗ Lr) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Bs ⊗ Ls) ≫
        (ordinaryFinitePullback A (q ≫ p)).map (b.hom ⊗ₘ c) := by
    exact (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.naturality
      (b.hom ⊗ₘ c)
  have he : (ordinaryFinitePullback A (ProjectiveLine.affineChart X)).map
        (((ordinaryFinitePullback A (ProjectiveLine X ↘ X)).obj Ks) ◁ cp) ≫
        (affineTraceLineRight A Nr hr X).map z =
      (ordinaryFinitePullback A (ProjectiveLine.affineChart X)).map
        ((ordinaryFinitePullback A (ProjectiveLine X ↘ X)).map z ⊗ₘ cp) := by
    exact map_tensor_whiskers (ordinaryFinitePullback A (ProjectiveLine X ↘ X))
      (ordinaryFinitePullback A (ProjectiveLine.affineChart X)) z cp
  let dr := (affineLinearLineDescent A Nr hr
    tr X
    (affineTraceInvertible Nr T hTr d) Kr).hom
  let ds := (affineLinearLineDescent A Ns hs
    ts X
    (affineTraceInvertible Ns T hTs d) Ks).hom
  let nr := (affineLinearCoefficientDescent A Nr hr
    tr T
    hTr (d + 1)).hom
  let ns := (affineLinearCoefficientDescent A Ns hs
    ts T
    hTs (d + 1)).hom
  let mr := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Br ⊗ Lr)
  let ms := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p).inv.app (Bs ⊗ Ls)
  have hnr : nr = dr ≫ (ordinaryFinitePullback A q).map αr ≫ mr := by
    exact tower_descent_succ_hom A Nr hr tr
      T hTr d
  have hns : ns = ds ≫ (ordinaryFinitePullback A q).map αs ≫ ms := by
    exact tower_descent_succ_hom A Ns hs ts
      T hTs d
  exact paste_descent_successor (ordinaryFinitePullback A q)
    ((ordinaryFinitePullback A (ProjectiveLine.affineChart X)).map
      (((ordinaryFinitePullback A (ProjectiveLine X ↘ X)).obj Ks) ◁ cp))
    ((affineTraceLineRight A Nr hr X).map z) _ dr ds (z ⊗ₘ cx) αr αs
    ((ordinaryFinitePullback A p).map (b.hom ⊗ₘ c)) mr ms _ nr ns hnr hns he hline ht hm

section Exponents
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

private abbrev canonicalTransport (r : ℕ)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :=
  Etale.projectiveLineTraceTransport (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hr

private abbrev canonicalDatum (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :=
  Etale.projectiveLineTraceDatum (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hr T
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1))

private theorem root_projective_trace
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (Etale.ordinaryFinitePushforward _ (ProjectiveLine T ↘ T)).map
        (integrationLineTransition l E n (ProjectiveLine T)
          (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom) r s hrs hr hs).hom ≫
      (canonicalDatum l E n T hT r hr).trace =
    (canonicalDatum l E n T hT s hs).trace := by
  have h := (integrationProjectiveExponentSquare l E n T hT r s hrs hr hs).1
  unfold IntegrationDecompositionSquare at h
  unfold kummerTraceOrdinaryDatum at h
  apply (cancel_epi (canonicalDatum l E n T hT s hs).decomposition.hom).mp
  simp only [Etale.OrdinaryFiniteP1Datum.trace, ← Category.assoc]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, biprod.map_snd, Category.comp_id, Category.id_comp]

private theorem root_projective_counit
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    (Etale.ordinaryFinitePushforward _ (ProjectiveLine T ↘ T)).map
        (((Etale.ordinaryFinitePullback _ (ProjectiveLine T ↘ T)).obj K) ◁
          (integrationLineTransition l E n (ProjectiveLine T)
            (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom) r s hrs hr hs).hom) ≫
      (canonicalDatum l E n T hT r hr).adjunction.counit.app K =
    (canonicalDatum l E n T hT s hs).adjunction.counit.app K := by
  let A := Scheme.finiteTateCoefficient l E n
  let q := ProjectiveLine T ↘ T
  let c := integrationLineTransition l E n (ProjectiveLine T)
    (by simpa using hT.map q.appTop.hom) r s hrs hr hs
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A q
  have hi : IsIso (Etale.ordinaryFiniteProjection A q
      ((Etale.ordinaryFiniteLine A (l ^ (s + 1)) hs (ProjectiveLine T))⟦(2 : ℤ)⟧) K) := by
    unfold Etale.ordinaryFiniteProjection
    infer_instance
  apply (cancel_epi (Etale.ordinaryFiniteProjection A q
    ((Etale.ordinaryFiniteLine A (l ^ (s + 1)) hs (ProjectiveLine T))⟦(2 : ℤ)⟧) K)).mp
  rw [← Category.assoc, projection_coefficient_naturality A q c.hom K,
    Category.assoc, (canonicalDatum l E n T hT r hr).counit_normalization K,
    (canonicalDatum l E n T hT s hs).counit_normalization K]
  change K ◁ _ ≫ K ◁ _ ≫ _ = K ◁ _ ≫ _
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  change K ◁ ((Etale.ordinaryFinitePushforward A q).map c.hom ≫
    (canonicalDatum l E n T hT r hr).trace) ≫ _ =
    K ◁ (canonicalDatum l E n T hT s hs).trace ≫ _
  rw [root_projective_trace]

private def rootLineStep (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    (Etale.affineTraceLineRight _ (l ^ (s + 1)) hs T).obj K ⟶
      (Etale.affineTraceLineRight _ (l ^ (r + 1)) hr T).obj K :=
  (Etale.ordinaryFinitePullback _ (ProjectiveLine.affineChart T)).map
    (((Etale.ordinaryFinitePullback _ (ProjectiveLine T ↘ T)).obj K) ◁
      (integrationLineTransition l E n (ProjectiveLine T)
        (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom) r s hrs hr hs).hom)

private theorem root_line_counit
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    (Etale.affineTraceLineLeft _ T).map (rootLineStep l E n T hT r s hrs hr hs K) ≫
      (Etale.affineTraceLineAdjunction _ (l ^ (r + 1)) hr
        (canonicalTransport l E n r hr) T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
        (canonicalDatum l E n T hT r hr)).counit.app K =
    (Etale.affineTraceLineAdjunction _ (l ^ (s + 1)) hs
      (canonicalTransport l E n s hs) T
      (by simpa only [Nat.cast_pow] using hT.pow (s + 1))
      (canonicalDatum l E n T hT s hs)).counit.app K := by
  let A := Scheme.finiteTateCoefficient l E n
  let q := ProjectiveLine T ↘ T
  let c := integrationLineTransition l E n (ProjectiveLine T)
    (by simpa using hT.map q.appTop.hom) r s hrs hr hs
  have hn := (Etale.affineTraceOpenAdjunction A T).counit.naturality
    (((Etale.ordinaryFinitePullback A q).obj K) ◁ c.hom)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [Etale.affineTraceLineAdjunction_counit, Etale.affineTraceLineAdjunction_counit]
  change (Etale.ordinaryFinitePushforward A q).map
      ((Etale.affineTraceOpenLeft A T).map
        ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map _)) ≫ _ ≫ _ = _
  let er := (Etale.affineTraceOpenAdjunction A T).counit.app
    ((Etale.ordinaryFiniteP1Right A (l ^ (r + 1)) hr T).obj K)
  let es := (Etale.affineTraceOpenAdjunction A T).counit.app
    ((Etale.ordinaryFiniteP1Right A (l ^ (s + 1)) hs T).obj K)
  let f := ((Etale.ordinaryFinitePullback A q).obj K) ◁ c.hom
  have he : (Etale.affineTraceOpenLeft A T).map
      ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map f) ≫ er =
      es ≫ f := hn
  calc
    _ = (Etale.ordinaryFinitePushforward A q).map
        ((Etale.affineTraceOpenLeft A T).map
          ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).map f) ≫ er) ≫
        (canonicalDatum l E n T hT r hr).adjunction.counit.app K := by
      rw [Functor.map_comp, Category.assoc]
    _ = (Etale.ordinaryFinitePushforward A q).map (es ≫ f) ≫
        (canonicalDatum l E n T hT r hr).adjunction.counit.app K := by rw [he]
    _ = (Etale.ordinaryFinitePushforward A q).map es ≫
        ((Etale.ordinaryFinitePushforward A q).map f ≫
          (canonicalDatum l E n T hT r hr).adjunction.counit.app K) := by
      rw [Functor.map_comp, Category.assoc]
    _ = _ := by rw [root_projective_counit]

private theorem root_shifted_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (l : Γ(Y, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (Etale.ordinaryFinitePullback _ f).map
        (integrationLineTransition l E n Y hY r s hrs hr hs).hom ≫
      (Etale.ordinaryFiniteShiftedLinePullback _ (l ^ (r + 1)) hr
        (canonicalTransport l E n r hr) f
        (by simpa only [Nat.cast_pow] using hY.pow (r + 1))).hom =
    (Etale.ordinaryFiniteShiftedLinePullback _ (l ^ (s + 1)) hs
        (canonicalTransport l E n s hs) f
        (by simpa only [Nat.cast_pow] using hY.pow (s + 1))).hom ≫
      (integrationLineTransition l E n X (by simpa using hY.map f.appTop.hom)
        r s hrs hr hs).hom := by
  exact shiftedExponentTransition_pullback l E n f hY r s hrs hr hs
    (canonicalTransport l E n r hr) (canonicalTransport l E n s hs)

set_option maxHeartbeats 400000 in
-- Comparing the expanded tensor and pullback instances requires extra normalization.
private theorem root_line_descent
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K K' : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T)
    (f : K ⟶ K') :
    (Etale.ordinaryFinitePullback _ (ProjectiveLine.affineChart T)).map
        ((Etale.ordinaryFinitePullback _ (ProjectiveLine T ↘ T)).map f ⊗ₘ
          (integrationLineTransition l E n (ProjectiveLine T)
            (by simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom) r s hrs hr hs).hom) ≫
      (Etale.affineLinearLineDescent _ (l ^ (r + 1)) hr
        (canonicalTransport l E n r hr) T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) K').hom =
    (Etale.affineLinearLineDescent _ (l ^ (s + 1)) hs
        (canonicalTransport l E n s hs) T
        (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) K).hom ≫
      (Etale.ordinaryFinitePullback _ (AffineSpace PUnit.{u + 1} T ↘ T)).map
        (f ⊗ₘ (integrationLineTransition l E n T hT r s hrs hr hs).hom) := by
  let A := Scheme.finiteTateCoefficient l E n
  let j := ProjectiveLine.affineChart T
  let p := AffineSpace PUnit.{u + 1} T ↘ T
  let hP : IsUnit (l : Γ(ProjectiveLine T, ⊤)) := by
    simpa using hT.map (ProjectiveLine T ↘ T).appTop.hom
  exact line_descent_naturality A (l ^ (r + 1)) (l ^ (s + 1)) hr hs
    (canonicalTransport l E n r hr) (canonicalTransport l E n s hs) T
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
    (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) K K' f
    (integrationLineTransition l E n T hT r s hrs hr hs).hom
    (integrationLineTransition l E n (ProjectiveLine T) hP r s hrs hr hs).hom
    (integrationLineTransition l E n (AffineSpace PUnit.{u + 1} T)
      (by simpa using hT.map p.appTop.hom) r s hrs hr hs).hom
    (root_shifted_pullback l E n j hP r s hrs hr hs)
    (root_shifted_pullback l E n p hT r s hrs hr hs)

private lemma root_base_succ_iso
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    baseExponentComparison l E n T hT r s hrs hr hs (d + 1) =
      ordinaryFiniteTensorRightMapIso _ T
        (baseExponentComparison l E n T hT r s hrs hr hs d)
        ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
          (exponentTransition l E n T hT r s hrs hr hs 1))) := by
  with_unfolding_all rfl

private lemma root_base_succ_hom
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (baseExponentComparison l E n T hT r s hrs hr hs (d + 1)).hom =
      (baseExponentComparison l E n T hT r s hrs hr hs d).hom ⊗ₘ
        (integrationLineTransition l E n T hT r s hrs hr hs).hom := by
  simp only [root_base_succ_iso, tensor_iso_hom, Functor.mapIso_hom]
  rfl

set_option maxHeartbeats 400000 in
-- The recursive tower changes the definitional presentation of the stage schemes.
private theorem root_tower_descent_succ
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    rootLineStep l E n (affineTraceTower T d)
        (by simpa using hT.map (affineTraceProjection T d).appTop.hom) r s hrs hr hs
        ((affineTraceRight _ (l ^ (s + 1)) hs T d).obj (ordinaryFiniteUnit _ T)) ≫
      (affineTraceLineRight _ (l ^ (r + 1)) hr (affineTraceTower T d)).map
        (integrationTowerTransition l E n T hT r s hrs hr hs d).hom ≫
      (affineLinearCoefficientDescent _ (l ^ (r + 1)) hr
        (canonicalTransport l E n r hr) T
        (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) (d + 1)).hom =
    (affineLinearCoefficientDescent _ (l ^ (s + 1)) hs
        (canonicalTransport l E n s hs) T
        (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) (d + 1)).hom ≫
      (ordinaryFinitePullback _ (affineTraceProjection T (d + 1))).map
        (baseExponentComparison l E n T hT r s hrs hr hs (d + 1)).hom := by
  let A := Scheme.finiteTateCoefficient l E n
  let X := affineTraceTower T d
  let hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa using hT.map (affineTraceProjection T d).appTop.hom
  let Ks := (affineTraceRight A (l ^ (s + 1)) hs T d).obj (ordinaryFiniteUnit A T)
  let Kr := (affineTraceRight A (l ^ (r + 1)) hr T d).obj (ordinaryFiniteUnit A T)
  have h := tower_descent_successor_of_squares A (l ^ (r + 1)) (l ^ (s + 1)) hr hs
    (canonicalTransport l E n r hr) (canonicalTransport l E n s hs) T
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
    (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) d
    (baseExponentComparison l E n T hT r s hrs hr hs d)
    (integrationLineTransition l E n T hT r s hrs hr hs).hom
    (integrationLineTransition l E n X hX r s hrs hr hs).hom
    (integrationLineTransition l E n (ProjectiveLine X)
      (by simpa using hX.map (ProjectiveLine X ↘ X).appTop.hom) r s hrs hr hs).hom
    (root_shifted_pullback l E n (affineTraceProjection T d) hT r s hrs hr hs)
    (root_line_descent l E n X hX r s hrs hr hs Ks Kr
      (integrationTowerTransition l E n T hT r s hrs hr hs d).hom)
  exact h.trans (congrArg (fun k =>
    (affineLinearCoefficientDescent A (l ^ (s + 1)) hs (canonicalTransport l E n s hs)
      T (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) (d + 1)).hom ≫
      (ordinaryFinitePullback A (affineTraceProjection T (d + 1))).map k)
    (root_base_succ_hom l E n T hT r s hrs hr hs d).symm)

end Exponents

set_option maxHeartbeats 400000 in
-- The induction identifies recursive tower functors with their successor composites.
end AlgebraicGeometry.ProEtale.VectorIntegrationSite
