/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarCompositeModelPasting
public import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization
import all WeilConjectures.AlgebraicGeometry.ProperOpenCoefficientRefinement
import all WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Scalar extension and compactification refinements -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  scalarDirectImageMate derivedOpenImmersionShriekIso

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local instance_reducible] scalarSixPull CommMon.toMon
  moduleObjectDerivedPushforward
private theorem x5_scalarDenseRing_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X :=
  Λ.comm

private theorem x5_scalarDenseMap_isMonHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local instance] x5_scalarDenseRing_comm x5_scalarDenseMap_isMonHom

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private abbrev x5_dense_open_scalar_iso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙ scalarSixChange a Z ≅
      scalarSixChange a X ⋙ (openImmersionLowerShriek Λ'.X j).mapDerivedCategory := by
  with_unfolding_all
    exact @derivedOpenImmersionShriekIso.{u} Λ.X Λ'.X Λ.mon Λ.comm Λ'.mon Λ'.comm
      a.hom.hom a.hom.isMonHom_hom X Z j inferInstance

private theorem x5_open_scalar_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {P : B ⥤ A} {J' : C ⥤ D} {P' : D ⥤ C}
    {TX : A ⥤ C} {RX : C ⥤ A} {TZ : B ⥤ D} {RZ : D ⥤ B}
    (a : J ⊣ P) (b : J' ⊣ P') (c : TX ⊣ RX) (d : TZ ⊣ RZ)
    (e : P' ⋙ RX ≅ RZ ⋙ P) (K : A) :
    b.unit.app (TX.obj K) ≫ P'.map
        (((conjugateIsoEquiv (c.comp b) (a.comp d)).symm e).inv.app K) =
      TX.map (a.unit.app K) ≫ (Adjunction.pushHomOfComapIso d c e).app (J.obj K) := by
  let δ := (conjugateIsoEquiv (c.comp b) (a.comp d)).symm e
  have he : conjugateEquiv (a.comp d) (c.comp b) δ.inv = e.inv := by
    exact congrArg Iso.inv ((conjugateIsoEquiv (c.comp b) (a.comp d)).apply_symm_apply e)
  have hm : (mateEquiv a b (.mk _ _ _ _ δ.inv)).natTrans =
      Adjunction.pushHomOfComapIso d c e := by
    have ht := iterated_mateEquiv_conjugateEquiv a b c d (.mk _ _ _ _ δ.inv)
    rw [he] at ht
    have hs : mateEquiv d c (mateEquiv a b (.mk _ _ _ _ δ.inv)) =
        .mk _ _ _ _ e.inv := by
      ext N
      exact congr_app ht N
    exact congrArg TwoSquare.natTrans ((mateEquiv d c).eq_symm_apply.mpr hs)
  have hu := unit_mateEquiv a b (.mk _ _ _ _ δ.inv) K
  change TX.map (a.unit.app K) ≫
      ((mateEquiv a b (.mk _ _ _ _ δ.inv)).natTrans).app (J.obj K) =
    b.unit.app (TX.obj K) ≫ P'.map (δ.inv.app K) at hu
  rw [hm] at hu
  exact hu.symm

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private theorem x5_condensed_open_scalar_unit {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j).unit.app
        ((scalarSixChange a X).obj K) ≫
      (scalarSixPull Λ' j).map
        ((x5_dense_open_scalar_iso a j).inv.app K) =
      (scalarSixChange a X).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app K) ≫
      (scalarDirectImagePullbackData.theta a j).hom.app
        ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj K) := by
  with_unfolding_all
    rw [scalarDirectImagePullbackData.thetaNormalization]
    exact x5_open_scalar_unit
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j)
      (scalarSixScalarAdjunction a X) (scalarSixScalarAdjunction a Z)
      (@derivedComapUpperStarIso.{u} Λ.X Λ'.X Λ.mon Λ.comm Λ'.mon Λ'.comm
        a.hom.hom a.hom.isMonHom_hom X Z j) K

private theorem x5_pull_triangle_scalar {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z W : Scheme.{u}} (i : X ⟶ Z) (h : Z ⟶ W) (j : X ⟶ W)
    (w : i ≫ h = j)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X W)) :
    let kA := Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ.X) w.symm) ≪≫ upperStarComp Λ.X i h) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar Λ.X h) (upperStar Λ.X i)
    let kB := Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (upperStar Λ'.X) w.symm) ≪≫ upperStarComp Λ'.X i h) ≪≫
      Functor.mapDerivedCategoryCompIso (upperStar Λ'.X h) (upperStar Λ'.X i)
    kB.hom.app ((scalarSixChange a W).obj N) ≫
        (scalarSixPull Λ' i).map ((scalarDirectImagePullbackData.theta a h).inv.app N) ≫
        (scalarDirectImagePullbackData.theta a i).inv.app ((scalarSixPull Λ h).obj N) =
      (scalarDirectImagePullbackData.theta a j).inv.app N ≫
        (scalarSixChange a X).map (kA.hom.app N) := by
  subst j
  dsimp only
  simp only [eqToIso_refl, Iso.refl_trans]
  have ho := IsIso.inv_eq_inv.mpr (scalarDirectImagePullbackData.composition a i h N)
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at ho
  change (scalarSixPullComp Λ' i h).hom.app _ ≫
      (scalarSixPull Λ' i).map ((scalarDirectImagePullbackData.theta a h).inv.app N) ≫
      (scalarDirectImagePullbackData.theta a i).inv.app ((scalarSixPull Λ h).obj N) =
    (scalarDirectImagePullbackData.theta a (i ≫ h)).inv.app N ≫
      (scalarSixChange a X).map ((scalarSixPullComp Λ i h).hom.app N)
  apply (cancel_mono ((scalarSixChange a X).map
    ((scalarSixPullComp Λ i h).inv.app N))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  have ht := congrArg (fun z ↦ (scalarSixPullComp Λ' i h).hom.app
      ((scalarSixChange a W).obj N) ≫ z) ho
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at ht
  rw [← ht]
  rw [(scalarSixChange a X).map_id ((scalarSixPull Λ (i ≫ h)).obj N)]
  exact (Category.comp_id ((scalarDirectImagePullbackData.theta a (i ≫ h)).inv.app N)).symm

-- Retain the unitors to match the definition of refinementOpenRestriction literally.
private theorem x5_restriction_mate_with_unitors
    {CA DA EA CB DB EB : Type*}
    [Category CA] [Category DA] [Category EA]
    [Category CB] [Category DB] [Category EB]
    {FA : EA ⥤ DA} {RA : DA ⥤ EA} {FB : EB ⥤ DB} {RB : DB ⥤ EB}
    (adjA : FA ⊣ RA) (adjB : FB ⊣ RB)
    (U₁A : DA ⥤ CA) (U₂A : EA ⥤ CA) (U₁B : DB ⥤ CB) (U₂B : EB ⥤ CB)
    (QX : CA ⥤ CB) (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB)
    (kA : U₂A ≅ FA ⋙ U₁A) (kB : U₂B ≅ FB ⋙ U₁B)
    (l₁ : Q₁ ⋙ U₁B ≅ U₁A ⋙ QX) (l₂ : Q₂ ⋙ U₂B ≅ U₂A ⋙ QX)
    (lv : Q₂ ⋙ FB ≅ FA ⋙ Q₁) (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB)
    (hc : ∀ M, FB.map (χ.app M) ≫ adjB.counit.app (Q₁.obj M) =
      lv.hom.app (RA.obj M) ≫ Q₁.map (adjA.counit.app M))
    (hk : ∀ N, kB.hom.app (Q₂.obj N) ≫ U₁B.map (lv.hom.app N) ≫
        l₁.hom.app (FA.obj N) = l₂.hom.app N ≫ QX.map (kA.hom.app N))
    (M : DA) :
    U₂B.map (χ.app M) ≫ kB.hom.app (RB.obj (Q₁.obj M)) ≫ 𝟙 _ ≫
        U₁B.map (adjB.counit.app (Q₁.obj M)) ≫ 𝟙 _ ≫ l₁.hom.app M =
      l₂.hom.app (RA.obj M) ≫ QX.map (kA.hom.app (RA.obj M)) ≫ QX.map (𝟙 _) ≫
        QX.map (U₁A.map (adjA.counit.app M)) ≫ QX.map (𝟙 _) := by
  simpa only [← Functor.map_comp, Category.id_comp, Category.comp_id] using
    AlgebraicGeometry.Etale.restriction_coefficient_mate adjA adjB U₁A U₂A U₁B U₂B
      QX Q₁ Q₂ kA kB l₁ l₂ lv χ hc hk M

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private theorem x5_restriction_scalar {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X d.obj.obj.Z)) :
    (scalarSixPull Λ' c.obj.obj.i).map ((scalarDirectImageMate a r.hom.hom.hom).app N) ≫
        (refinementOpenRestriction Λ'.X r.hom.hom).app
          ((scalarSixChange a d.obj.obj.Z).obj N) ≫
        (scalarDirectImagePullbackData.theta a d.obj.obj.i).inv.app N =
      (scalarDirectImagePullbackData.theta a c.obj.obj.i).inv.app
          ((RootCoordinateFace.lower Λ.X r.hom.hom.hom).obj N) ≫
        (scalarSixChange a X).map ((refinementOpenRestriction Λ.X r.hom.hom).app N) := by
  with_unfolding_all
    have hc := (scalarDirectImageMateCoherence a r.hom.hom.hom (𝟙 c.obj.obj.Z)).2.2.2.1
    have hk := x5_pull_triangle_scalar a d.obj.obj.i r.hom.hom.hom c.obj.obj.i
      r.hom.hom.i_hom
    have ht :=
      x5_restriction_mate_with_unitors
        (RootCoordinateFace.adjunction Λ.X r.hom.hom.hom)
        (RootCoordinateFace.adjunction Λ'.X r.hom.hom.hom)
        (scalarSixPull Λ d.obj.obj.i) (scalarSixPull Λ c.obj.obj.i)
        (scalarSixPull Λ' d.obj.obj.i) (scalarSixPull Λ' c.obj.obj.i)
        (scalarSixChange a X) (scalarSixChange a d.obj.obj.Z)
        (scalarSixChange a c.obj.obj.Z)
        (Functor.mapDerivedCategoryNatIso
            (eqToIso (congrArg (upperStar Λ.X) r.hom.hom.i_hom.symm) ≪≫
              upperStarComp Λ.X d.obj.obj.i r.hom.hom.hom) ≪≫
          Functor.mapDerivedCategoryCompIso _ _)
        (Functor.mapDerivedCategoryNatIso
            (eqToIso (congrArg (upperStar Λ'.X) r.hom.hom.i_hom.symm) ≪≫
              upperStarComp Λ'.X d.obj.obj.i r.hom.hom.hom) ≪≫
          Functor.mapDerivedCategoryCompIso _ _)
        (scalarDirectImagePullbackData.theta a d.obj.obj.i).symm
        (scalarDirectImagePullbackData.theta a c.obj.obj.i).symm
        (scalarDirectImagePullbackData.theta a r.hom.hom.hom).symm
        (scalarDirectImageMate a r.hom.hom.hom) hc hk N
    dsimp only [Iso.symm] at ht
    simpa only [refinementOpenRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
      Functor.map_comp, Category.assoc, Functor.comp_obj, Functor.id_obj,
      ← refinementAdjunction_eq, RootCoordinateFace.lower, moduleObjectDerivedPushforward,
      RootCoordinateFace.adjunction, Adjunction.ofNatIsoLeft_counit, scalarSixPull] using ht

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private theorem x5_local_refinement_scalar {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a c.obj.obj.Z).map (localizingRefinementMap Λ.X r K) ≫
        (scalarDirectImageMate a r.hom.hom.hom).app
          ((openImmersionLowerShriek Λ.X d.obj.obj.i).mapDerivedCategory.obj K) ≫
        (RootCoordinateFace.lower Λ'.X r.hom.hom.hom).map
          ((x5_dense_open_scalar_iso a d.obj.obj.i).hom.app K) =
      (x5_dense_open_scalar_iso a c.obj.obj.i).hom.app K ≫
        localizingRefinementMap Λ'.X r ((scalarSixChange a X).obj K) := by
  with_unfolding_all
    let := refinementOpenRestriction_isIso Λ'.X r
    exact AlgebraicGeometry.Etale.coefficient_refinement_of_restriction
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X d.obj.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X c.obj.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X d.obj.obj.i)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X c.obj.obj.i)
      (RootCoordinateFace.lower Λ.X r.hom.hom.hom)
      (RootCoordinateFace.lower Λ'.X r.hom.hom.hom)
      (scalarSixChange a X) (scalarSixChange a d.obj.obj.Z)
      (scalarSixChange a c.obj.obj.Z)
      (refinementOpenRestriction Λ.X r.hom.hom)
      (refinementOpenRestriction Λ'.X r.hom.hom)
      (scalarDirectImagePullbackData.theta a d.obj.obj.i).symm
      (scalarDirectImagePullbackData.theta a c.obj.obj.i).symm
      (scalarDirectImageMate a r.hom.hom.hom) (x5_restriction_scalar a r) K
      (localizingRefinementMap Λ.X r K)
      (localizingRefinementMap Λ'.X r ((scalarSixChange a X).obj K))
      ((x5_dense_open_scalar_iso a d.obj.obj.i).app K)
      ((x5_dense_open_scalar_iso a c.obj.obj.i).app K)
      (x5_condensed_open_scalar_unit a d.obj.obj.i K)
      (x5_condensed_open_scalar_unit a c.obj.obj.i K)
      (by
        dsimp only [Adjunction.homEquiv, Equiv.coe_fn_mk]
        simpa only [Functor.id_obj, Category.assoc] using
          localizingRefinementMap_normalized Λ.X r K)
      (by
        dsimp only [Adjunction.homEquiv, Equiv.coe_fn_mk]
        simpa only [Functor.id_obj, Category.assoc] using
          localizingRefinementMap_normalized Λ'.X r ((scalarSixChange a X).obj K))

private theorem x5_refinement_compositor_eq (Λ : ScalarSixRing.{u})
    {X Z Y : Scheme.{u}} (h : X ⟶ Z) (p : Z ⟶ Y) :
    refinementDerivedLowerStarComp Λ.X h p = RootCoordinateFace.lowerComp Λ.X h p := by
  apply Iso.ext_inv
  exact refinementComp_conjugate Λ.X h p

private theorem x5_derive_lowerStarCongr (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} {g h : X ⟶ Y} (w : g = h) :
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ.X w)).hom =
      (eqToIso (congrArg (fun g ↦ (lowerStar Λ.X g).rightDerivedFunctor) w)).hom := by
  cases w
  simp [lowerStarCongr, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans]

set_option maxHeartbeats 8000000 in
-- Comparing the existing derived functor presentations requires additional elaboration work.
private theorem x5_pushed_scalar_compositor {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z Y : Scheme.{u}} (h : X ⟶ Z) (p : Z ⟶ Y) (q : X ⟶ Y)
    (w : h ≫ p = q)
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Y).map
        ((refinementDerivedLowerStarComp Λ.X h p).inv.app N ≫
          (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ.X w)).hom.app N) ≫
        (scalarDirectImageMate a q).app N =
      (scalarDirectImageMate a p).app ((RootCoordinateFace.lower Λ.X h).obj N) ≫
        (RootCoordinateFace.lower Λ'.X p).map ((scalarDirectImageMate a h).app N) ≫
        (refinementDerivedLowerStarComp Λ'.X h p).inv.app
          ((scalarSixChange a X).obj N) ≫
        (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ'.X w)).hom.app
          ((scalarSixChange a X).obj N) := by
  with_unfolding_all
    subst q
    rw [x5_derive_lowerStarCongr, x5_derive_lowerStarCongr,
      x5_refinement_compositor_eq, x5_refinement_compositor_eq]
    simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    apply (cancel_mono ((RootCoordinateFace.lowerComp Λ'.X h p).hom.app
      ((scalarSixChange a X).obj N))).mp
    try simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [(scalarDirectImageMateCoherence a h p).2.1]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    rw [(scalarSixChange a Y).map_id
      (((lowerStar Λ.X h).rightDerivedFunctor ⋙
        (lowerStar Λ.X p).rightDerivedFunctor).obj N)]
    erw [Category.id_comp, Category.comp_id]

private theorem x5_push_refinement_pasting
    {DA EA YA DB EB YB : Type*}
    [Category DA] [Category EA] [Category YA]
    [Category DB] [Category EB] [Category YB]
    (RA : DA ⥤ EA) (RB : DB ⥤ EB)
    (P₁A : DA ⥤ YA) (P₂A : EA ⥤ YA) (P₁B : DB ⥤ YB) (P₂B : EB ⥤ YB)
    (Q₁ : DA ⥤ DB) (Q₂ : EA ⥤ EB) (QY : YA ⥤ YB)
    (γ₁ : P₁A ⋙ QY ⟶ Q₁ ⋙ P₁B) (γ₂ : P₂A ⋙ QY ⟶ Q₂ ⋙ P₂B)
    (χ : RA ⋙ Q₂ ⟶ Q₁ ⋙ RB) (κ : RA ⋙ P₂A ⟶ P₁A) (κ' : RB ⋙ P₂B ⟶ P₁B)
    (M₁A : DA) (M₂A : EA) (M₁B : DB) (M₂B : EB)
    (eA : M₂A ⟶ RA.obj M₁A) (eB : M₂B ⟶ RB.obj M₁B)
    (δ₁ : Q₁.obj M₁A ⟶ M₁B) (δ₂ : Q₂.obj M₂A ⟶ M₂B)
    (hκ : QY.map (κ.app M₁A) ≫ γ₁.app M₁A =
      γ₂.app (RA.obj M₁A) ≫ P₂B.map (χ.app M₁A) ≫ κ'.app (Q₁.obj M₁A))
    (he : Q₂.map eA ≫ χ.app M₁A ≫ RB.map δ₁ = δ₂ ≫ eB) :
    QY.map (P₂A.map eA ≫ κ.app M₁A) ≫ γ₁.app M₁A ≫ P₁B.map δ₁ =
      (γ₂.app M₂A ≫ P₂B.map δ₂) ≫ P₂B.map eB ≫ κ'.app M₁B := by
  have hn := γ₂.naturality eA
  have hk := κ'.naturality δ₁
  dsimp only [Functor.comp_map] at hn hk
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hκ, reassoc_of% hn, ← hk]
  have hm := congrArg P₂B.map he
  simp only [Functor.map_comp] at hm
  rw [reassoc_of% hm]


set_option maxHeartbeats 8000000 in
-- Keep the adopted derived adjunction presentations folded during elaboration.
/-- The coefficient comparison commutes with every boundary-preserving refinement.
Source: latest blueprint, scalar-six compact-support proof, Independence and Composition.
(blueprint: lem-sfb-scalar-refinement-pasting).

Proof: write the refinement component as the proper image of the open-adjunction map, followed by
the
inverse proper compositor and equality transport. The derived proper compositor equals the
adjunction-normalized one by its conjugate formula. Move the coefficient mate across equality
transport, then apply its geometric composition law and naturality. Naturality of the primed
proper compositor puts all open factors inside the same proper image. Apply
the existing generic local_refinement_scalar to those factors; functoriality gives precisely the
primed refinement
component. The argument applies to all boundary refinements, with no density assumption. -/
theorem scalarRefinementPasting {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Y).map (compactificationRefinementComponent Λ.X r K) ≫
      sfbScalarCompactComparison a d.obj.obj.i d.obj.obj.g K =
    sfbScalarCompactComparison a c.obj.obj.i c.obj.obj.g K ≫
      compactificationRefinementComponent Λ'.X r ((scalarSixChange a X).obj K) := by
  with_unfolding_all
    classical
    let J := (openImmersionLowerShriek Λ.X d.obj.obj.i).mapDerivedCategory.obj K
    let J' := (openImmersionLowerShriek Λ'.X d.obj.obj.i).mapDerivedCategory.obj
      ((scalarSixChange a X).obj K)
    let κ := (refinementDerivedLowerStarComp Λ.X r.hom.hom.hom c.obj.obj.g).inv ≫
      (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ.X r.hom.hom.hom_g)).hom
    let κ' := (refinementDerivedLowerStarComp Λ'.X r.hom.hom.hom c.obj.obj.g).inv ≫
      (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ'.X r.hom.hom.hom_g)).hom
    have hp := x5_pushed_scalar_compositor a r.hom.hom.hom c.obj.obj.g
      d.obj.obj.g r.hom.hom.hom_g J
    change (scalarSixChange a Y).map
        ((RootCoordinateFace.lower Λ.X c.obj.obj.g).map
          (localizingRefinementMap Λ.X r K) ≫ κ.app J) ≫
        (scalarDirectImageMate a d.obj.obj.g).app J ≫
        (RootCoordinateFace.lower Λ'.X d.obj.obj.g).map
          ((x5_dense_open_scalar_iso a d.obj.obj.i).hom.app K) =
      ((scalarDirectImageMate a c.obj.obj.g).app _ ≫
        (RootCoordinateFace.lower Λ'.X c.obj.obj.g).map
          ((x5_dense_open_scalar_iso a c.obj.obj.i).hom.app K)) ≫
        (RootCoordinateFace.lower Λ'.X c.obj.obj.g).map
          (localizingRefinementMap Λ'.X r ((scalarSixChange a X).obj K)) ≫ κ'.app J'
    exact x5_push_refinement_pasting
      (RootCoordinateFace.lower Λ.X r.hom.hom.hom)
      (RootCoordinateFace.lower Λ'.X r.hom.hom.hom)
      (RootCoordinateFace.lower Λ.X d.obj.obj.g)
      (RootCoordinateFace.lower Λ.X c.obj.obj.g)
      (RootCoordinateFace.lower Λ'.X d.obj.obj.g)
      (RootCoordinateFace.lower Λ'.X c.obj.obj.g)
      (scalarSixChange a d.obj.obj.Z) (scalarSixChange a c.obj.obj.Z)
      (scalarSixChange a Y)
      (scalarDirectImageMate a d.obj.obj.g) (scalarDirectImageMate a c.obj.obj.g)
      (scalarDirectImageMate a r.hom.hom.hom) κ κ' J _ J' _
      (localizingRefinementMap Λ.X r K)
      (localizingRefinementMap Λ'.X r ((scalarSixChange a X).obj K))
      ((x5_dense_open_scalar_iso a d.obj.obj.i).hom.app K)
      ((x5_dense_open_scalar_iso a c.obj.obj.i).hom.app K)
      hp (x5_local_refinement_scalar a r K)

end AlgebraicGeometry.ProEtale.CondensedRing
