/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactPullbackComparisonMonoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit

/-! # Normalization of the exact condensed projection adjunctions

Source: Stacks Tags 07A4, 0D6D and 0E8I; the proper and open adjunction
normalizations in steps 3--4 of lem-sf-condensed-projection-factor-scalar-identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

private theorem projectionTransport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F F' : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) (e : F ≅ F')
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (φ' : (Functor.postcompose₂.obj F').obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F').obj F').obj (curriedTensor C))
    (h : ∀ A B, e.inv.app (A ⊗ B) ≫ (φ.app A).app B =
      (φ'.app A).app B ≫ (e.inv.app A ▷ F'.obj B) ≫ (F.obj A ◁ e.inv.app B))
    (M : C) (N : D) :
    ((adj.rightAdjointProjectionMap φ).app M).app N ≫
        G.map (M ◁ e.hom.app N) =
      (((adj.ofNatIsoLeft e).rightAdjointProjectionMap φ').app M).app N := by
  let π : G.obj M ⊗ N ⟶ G.obj (M ⊗ F.obj N) :=
    ((adj.rightAdjointProjectionMap φ).app M).app N
  let π' : G.obj M ⊗ N ⟶ G.obj (M ⊗ F'.obj N) :=
    (((adj.ofNatIsoLeft e).rightAdjointProjectionMap φ').app M).app N
  change π ≫ G.map (M ◁ e.hom.app N) = π'
  have hi : conjugateEquiv adj (adj.ofNatIsoLeft e) e.inv = 𝟙 G := by
    ext X
    simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit,
      ← Functor.map_comp, Category.assoc]
  have hc := adj.rightAdjointProjectionMap_conjugate φ (adj.ofNatIsoLeft e) φ' e.inv h M N
  rw [hi] at hc
  simp only [NatTrans.id_app, curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map] at hc
  change 𝟙 (G.obj M ⊗ N) ≫ π' ≫ G.map (M ◁ e.inv.app N) =
    π ≫ 𝟙 (G.obj (M ⊗ F.obj N)) at hc
  rw [Category.id_comp, Category.comp_id] at hc
  have hinv : G.map (M ◁ e.inv.app N) ≫ G.map (M ◁ e.hom.app N) = 𝟙 _ := by
    rw [← G.map_comp, ← whiskerLeft_comp, Iso.inv_hom_id_app,
      whiskerLeft_id, G.map_id]
  calc
    π ≫ G.map (M ◁ e.hom.app N) =
        (π' ≫ G.map (M ◁ e.inv.app N)) ≫ G.map (M ◁ e.hom.app N) := by rw [hc]
    _ = π' := by rw [Category.assoc, hinv, Category.comp_id]

private theorem leftProjectionTransport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {J : C ⥤ D} {S E : D ⥤ C} (aS : J ⊣ S) (aE : J ⊣ E) (e : S ≅ E)
    (δE : (((Functor.whiskeringLeft₂ C).obj E).obj E).obj (curriedTensor C) ⟶
      (Functor.postcompose₂.obj E).obj (curriedTensor D))
    (dS : ∀ M N : D, S.obj M ⊗ S.obj N ⟶ S.obj (M ⊗ N))
    (hu : ∀ K, aS.unit.app K ≫ e.hom.app (J.obj K) = aE.unit.app K)
    (hd : ∀ M N, (e.hom.app M ▷ E.obj N) ≫ (δE.app M).app N =
      (S.obj M ◁ e.inv.app N) ≫ dS M N ≫ e.hom.app (M ⊗ N))
    (K : C) (N : D) :
    ((aE.projectionMap E (curriedTensor C) (curriedTensor D) δE).app K).app N =
      J.map (K ◁ e.inv.app N) ≫
        (aS.homEquiv (K ⊗ S.obj N) (J.obj K ⊗ N)).symm
          ((aS.unit.app K ▷ S.obj N) ≫ dS (J.obj K) N) := by
  apply (aE.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  rw [aE.unit_app_comp_map_projectionMap_app_app]
  change (aE.unit.app K ▷ E.obj N) ≫ (δE.app (J.obj K)).app N =
    aE.unit.app (K ⊗ E.obj N) ≫ E.map (J.map (K ◁ e.inv.app N)) ≫
      E.map ((aS.homEquiv (K ⊗ S.obj N) (J.obj K ⊗ N)).symm
        ((aS.unit.app K ▷ S.obj N) ≫ dS (J.obj K) N))
  rw [aE.unit_naturality_assoc (K ◁ e.inv.app N)]
  rw [← hu (K ⊗ S.obj N)]
  rw [Category.assoc, ← e.hom.naturality]
  rw [← Category.assoc (aS.unit.app (K ⊗ S.obj N)),
    ← aS.homEquiv_unit (K ⊗ S.obj N) (J.obj K ⊗ N)
      ((aS.homEquiv (K ⊗ S.obj N) (J.obj K ⊗ N)).symm
        ((aS.unit.app K ▷ S.obj N) ≫ dS (J.obj K) N)), Equiv.apply_symm_apply]
  rw [← hu K, comp_whiskerRight, Category.assoc, hd]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  rfl

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The published total-derived pullback tensorator transported to exact pullback.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-sf-condensed-projection-adjunction-normalization). -/
def condensedProjectionPullTensor (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (scalarSixPull Λ f)).obj (curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj (scalarSixPull Λ f)).obj
        (scalarSixPull Λ f)).obj (curriedTensor _) :=
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ.X f
  (Functor.postcompose₂.mapIso e.symm).app (curriedTensor _) ≪≫
    leftDerivedUpperStarTensorIso Λ.X f ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso e).app
      (upperStar Λ.X f).leftDerivedFunctor).app (curriedTensor _) ≪≫
    (((Functor.whiskeringLeft₂ _).obj (scalarSixPull Λ f)).mapIso e).app
      (curriedTensor _)

set_option maxHeartbeats 1600000 in
-- Compare the two exact derived adjunctions on homotopy representatives.
private theorem openSupportAdjunction_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openSupportDerivedAdjunction Λ j).unit ≫
        Functor.whiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ j)).hom =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let a := openImmersionLowerShriekUpperStarAdjunction Λ j
  let s := supportPullbackIsoUpperStar Λ j
  rw [openSupportDerivedAdjunction, CategoryTheory.Adjunction.mapDerived_eq]
  change (a.ofNatIsoRight s.symm).mapDerivedCategoryAdjunction.unit ≫
      Functor.whiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso s).hom = a.mapDerivedCategoryAdjunction.unit
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (supportModules Λ X) (.up ℤ))
  intro H
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono ((upperStar Λ j).mapDerivedCategory.map
      ((openImmersionLowerShriek Λ j).mapDerivedCategoryFactorsh.hom.app H) ≫
    (upperStar Λ j).mapDerivedCategoryFactorsh.hom.app
      (((openImmersionLowerShriek Λ j).mapHomotopyCategory (.up ℤ)).obj H))).mp
  simp only [Category.assoc]
  rw [← (Functor.mapDerivedCategoryNatIso s).hom.naturality_assoc]
  dsimp only [Functor.comp_obj]
  erw [Functor.mapDerivedCategoryNatIso_fach]
  rw [CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj_assoc,
    CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj,
    ← Functor.map_comp]
  congr 1
  obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient,
    NatTrans.mapHomotopyCategory_app, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  simp only [a, s, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  change (a.unit.app (C.X n) ≫ s.inv.app
      ((openImmersionLowerShriek Λ j).obj (C.X n))) ≫
      s.hom.app ((openImmersionLowerShriek Λ j).obj (C.X n)) = a.unit.app (C.X n)
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id (a.unit.app (C.X n))


set_option maxHeartbeats 1600000 in
-- Components of the chosen transport are the usual conjugated tensorator; unfolding by
-- simp lemmas instead of a `change` to the whole composite saves about 30 s of elaboration.
private theorem pullTensor_hom (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    ((condensedProjectionPullTensor Λ f).hom.app A).app B =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv.app (A ⊗ B) ≫
        ((leftDerivedUpperStarTensor Λ.X f).app A).app B ≫
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app A ⊗ₘ
          (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app B) := by
  simp only [scalarSixPull, Functor.postcompose₂_obj_obj_obj_obj, curriedTensor_obj_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, condensedProjectionPullTensor,
    Functor.mapIso_symm, leftDerivedUpperStarTensorIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_inv, asIso_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Functor.postcompose₂_map_app_app_app, Functor.whiskeringLeft₂_map_app_app_app_app,
    curriedTensor_map_app, Functor.whiskeringLeft₂_obj_map_app_app_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def]

set_option maxHeartbeats 1600000 in
-- Take inverses of the pointwise tensor transport identity.
private theorem pullTensor_inv (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    ((condensedProjectionPullTensor Λ f).inv.app A).app B =
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv.app A ⊗ₘ
        (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).inv.app B) ≫
      (((leftDerivedUpperStarTensorIso Λ.X f).app A).app B).inv ≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app (A ⊗ B) := by
  have hi : ((condensedProjectionPullTensor Λ f).app A).app B =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).symm.app (A ⊗ B) ≪≫
        ((leftDerivedUpperStarTensorIso Λ.X f).app A).app B ≪≫
        tensorIso ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).app A)
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).app B) :=
    Iso.ext (pullTensor_hom Λ f A B)
  simpa only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.app_inv, Category.assoc]
    using congrArg Iso.inv hi

set_option maxHeartbeats 1600000 in
-- The exact direct-image adjunction is the transported total-derived adjunction.
private theorem properNormalization (Λ : ScalarSixRing.{u})
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    moduleObjectProjectionMap Λ.X p M N ≫
        (RootCoordinateFace.lower Λ.X p).map
          (M ◁ (leftDerivedUpperStarIsoMapDerivedCategory Λ.X p).hom.app N) =
      (((RootCoordinateFace.adjunction Λ.X p).rightAdjointProjectionMap
        (condensedProjectionPullTensor Λ p).hom).app M).app N := by
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ.X p
  have he : RootCoordinateFace.adjunction Λ.X p =
      (derivedUpperStarLowerStarAdjunction Λ.X p).ofNatIsoLeft e :=
    CategoryTheory.Adjunction.mapDerived_eq _ _ (upperStarLowerStarAdjunction Λ.X p)
  rw [he]
  have h := projectionTransport (derivedUpperStarLowerStarAdjunction Λ.X p) e
    (leftDerivedUpperStarTensor Λ.X p) (condensedProjectionPullTensor Λ p).hom (by
      intro A B
      rw [pullTensor_hom]
      simp only [e, ← MonoidalCategory.tensorHom_def, Category.assoc,
        tensorHom_comp_tensorHom, Iso.hom_inv_id_app, id_tensorHom_id]
      let δ : (upperStar Λ.X p).leftDerivedFunctor.obj (A ⊗ B) ⟶
          (upperStar Λ.X p).leftDerivedFunctor.obj A ⊗
            (upperStar Λ.X p).leftDerivedFunctor.obj B :=
        ((leftDerivedUpperStarTensor Λ.X p).app A).app B
      change e.inv.app (A ⊗ B) ≫ δ = e.inv.app (A ⊗ B) ≫ (δ ≫ 𝟙 _)
      exact congrArg (fun v ↦ e.inv.app (A ⊗ B) ≫ v) (Category.comp_id δ).symm) M N
  simpa only [moduleObjectProjectionMap, moduleObjectProjectionData,
    RootCoordinateFace.lower, moduleObjectDerivedPushforward, derivedTensor, e] using h

set_option maxHeartbeats 1600000 in
-- The existing exact comparison theorem determines the inverse support tensorator.
private theorem supportTensorInverse (Λ : ScalarSixRing.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (supportDerivedTensorComparison Λ.X f A B).inv ≫
        (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).hom.app
          (A ⊗ B) =
      ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).hom.app A ⊗ₘ
        (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X f)).hom.app B) ≫
        ((condensedProjectionPullTensor Λ f).inv.app A).app B := by
  let c := supportPullbackExactComparison Λ.X f
  have hh := (exact_pullback_comparison_monoidal Λ.X f).1 A B
  have hi : c.app (A ⊗ B) ≪≫ supportDerivedTensorComparison Λ.X f A B =
      ((leftDerivedUpperStarTensorIso Λ.X f).app A).app B ≪≫
        tensorIso (c.app A) (c.app B) := Iso.ext hh
  have ht := congrArg (fun z ↦ z ≫
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app (A ⊗ B))
      (congrArg Iso.inv hi)
  have hc : modulePullbackExactComparison Λ.X f =
      leftDerivedUpperStarIsoMapDerivedCategory Λ.X f := rfl
  simp only [pullTensor_inv]
  simpa only [c, supportPullbackExactComparison, Iso.trans_inv, Iso.symm_inv,
    tensorIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc,
    hc, NatTrans.comp_app,
    ← tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id] using ht


set_option maxHeartbeats 1600000 in
-- Apply generic left-adjoint transport to the computed unit and tensor identities.
private theorem openNormalization (Λ : ScalarSixRing.{u})
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).projectionMap
        (scalarSixPull Λ j) (curriedTensor _) (curriedTensor _)
        (condensedProjectionPullTensor Λ j).inv).app K).app N =
      (openImmersionLowerShriek Λ.X j).mapDerivedCategory.map
        (K ◁ (Functor.mapDerivedCategoryNatIso
          (supportPullbackIsoUpperStar Λ.X j)).inv.app N) ≫
        openSupportProjection Λ.X j K N := by
  let s := Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X j)
  have h := leftProjectionTransport (openSupportDerivedAdjunction Λ.X j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j) s
    (condensedProjectionPullTensor Λ j).inv
    (fun M N ↦ (supportDerivedTensorComparison Λ.X j M N).inv)
    (by
      intro A
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app]
        using NatTrans.congr_app (openSupportAdjunction_unit Λ.X j) A)
    (by
      intro A B
      dsimp only [s]
      rw [supportTensorInverse]
      simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
        Iso.inv_hom_id_app, tensorHom_id]) K N
  simpa only [openSupportProjection, derivedTensor, scalarSixPull, s,
    curriedTensor_map_app, curriedTensor_obj_obj] using h


attribute [-instance] ring_comm

/-- Transporting the two specified projections to exact pullback agrees with their
abstract adjunction definitions. This assertion involves no coefficient change.

Source: Stacks 07A4, 0D6D and 0E8I; parent proof steps 3--4
(blueprint: lem-sf-condensed-projection-adjunction-normalization).

Proof: compute the transported tensorator on its two arguments. The proved
mapDerived_eq identity identifies the exact geometric adjunction with transport of
the total-derived adjunction. Right-adjoint projection conjugation then gives the
proper clause after cancelling the comparison components. For the open clause,
compare the two exact derived units after localization and the canonical exact
factorizations. Their degreewise equality is the ordinary ofNatIsoRight unit formula.
The existing exact_pullback_comparison_monoidal tensor equation identifies the
support tensorator with transport of the total-derived tensorator. Invert that
equation and transpose along the exact open adjunction. Naturality of the support
comparison and its inverse identities give the stated open projection equation.
These computations include empty opens and zero coefficient rings. -/
theorem condensedProjectionAdjunctionNormalization (Λ : ScalarSixRing.{u}) :
    (∀ {Z Y : Scheme.{u}} (p : Z ⟶ Y)
      (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z))
      (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
      moduleObjectProjectionMap Λ.X p M N ≫
          (RootCoordinateFace.lower Λ.X p).map
            (M ◁ (leftDerivedUpperStarIsoMapDerivedCategory Λ.X p).hom.app N) =
        (((RootCoordinateFace.adjunction Λ.X p).rightAdjointProjectionMap
          (condensedProjectionPullTensor Λ p).hom).app M).app N) ∧
    (∀ {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
      (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)),
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).projectionMap
          (scalarSixPull Λ j) (curriedTensor _) (curriedTensor _)
          (condensedProjectionPullTensor Λ j).inv).app K).app N =
        (openImmersionLowerShriek Λ.X j).mapDerivedCategory.map
          (K ◁ (Functor.mapDerivedCategoryNatIso
            (supportPullbackIsoUpperStar Λ.X j)).inv.app N) ≫
          openSupportProjection Λ.X j K N) := by
  constructor
  · intro Z Y p M N
    exact properNormalization Λ p M N
  · intro X Z j _ K N
    exact openNormalization Λ j K N

end AlgebraicGeometry.ProEtale.CondensedRing
