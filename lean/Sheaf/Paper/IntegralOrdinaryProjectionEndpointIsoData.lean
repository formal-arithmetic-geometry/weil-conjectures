/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap

import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import all Sheaf.Paper.SfCompleteDirectImageReduction
import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange
import Sheaf.Paper.FiniteScalarTensorRealization
import Sheaf.Paper.FiniteScalarPullbackComparison

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] sfIntrinsicModuleEquivalence sfIntrinsicDerivedEquivalence
  ProEtale.projectionMapOfCompactification
attribute [local instance 100000] SheafOfModules.instAbelian
attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

/-! Endpoint comparison data for the ordinary projection. -/

/-- The two endpoint comparison isomorphisms used by the ordinary projection square.
Source: the endpoint comparison step of `lem-sf-ordinary-projection-reduction-arrow-comparison`.
(blueprint: lem-sf-ordinary-projection-endpoint-iso-data-q2). -/
structure IntegralOrdinaryProjectionEndpointData
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) where
  s : let A := Padic.coefficientExtensionRing l E (n + 1)
      letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
      (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L))).left ≅
      (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))).left
  t : let A := Padic.coefficientExtensionRing l E (n + 1)
      letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
      (Arrow.mk ((scalarReductionDerivedExtension l E Y n).map
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K).app L))).right ≅
      (Arrow.mk ((sfIntrinsicDerivedEquivalence Y A).functor.map
        (((ProEtale.projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj
              ((scalarReductionDerivedExtension l E X n).obj K))).app
            ((sfIntrinsicDerivedEquivalence Y A).inverse.obj
              ((scalarReductionDerivedExtension l E Y n).obj L))))).right

private theorem completedPush_eq
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    proEtaleRingModuleDirectImage g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull g) = sfCompletedModuleDirectImage l E g := by
  have h : proEtaleRingDirectImageMap g
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull g) = sfCompletedCoefficientMap l E g := by
    exact ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
  rw [h]

private noncomputable def reductionOpenIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
      ((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E) j).mapDerivedCategory.obj K) ≅
    (PurCompactSupport.openExtension
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) j).mapDerivedCategory.obj
        ((scalarReductionDerivedExtension l E X n).obj K) := by
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
  have := PurCompactSupport.openComparison_isIso a j K
  exact ((PurCompactSupport.finiteReductionIso l E Y n).app _).symm ≪≫
    asIso ((PurCompactSupport.openComparison a j).app K) ≪≫
      (PurCompactSupport.openExtension
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) j).mapDerivedCategory.mapIso
          ((PurCompactSupport.finiteReductionIso l E X n).app K)

private noncomputable def reductionImageIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K) ≅
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      ((scalarReductionDerivedExtension l E X n).obj K) := by
  letI : (sfCompletedModuleDirectImage l E c.g).Additive :=
    sfCompletedModuleDirectImage_additive l E c.g
  letI : (proEtaleConstantModuleDirectImage c.g
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    proEtaleConstantModuleDirectImage_additive c.g _
  let M := (PurCompactSupport.openExtension
    (PurCompactSupport.completed l E) c.i).mapDerivedCategory.obj K
  have := sf_projection_formula l E c.g n M
  let h := Functor.rightDerivedFunctorNatIso (eqToIso (completedPush_eq l E c.g))
  refine (scalarReductionDerivedExtension l E Y n).mapIso (h.app M) ≪≫
    asIso (sf_projection_map l E c.g n M) ≪≫ ?_
  exact (proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        (reductionOpenIso l E c.i K n) ≪≫
    ((Functor.rightDerivedFunctorNatIso
      (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n c.g))).app _).symm ≪≫
    (PurCompactSupport.finiteImageIso l E n c).app _

private noncomputable def reductionTensorIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u})
    (a : ProEtaleTensorModel W ((PurCompactSupport.completed l E).ring W))
    (n : ℕ) (b : ProEtaleTensorModel W
      (proEtaleConstantRing W (Padic.coefficientExtensionRing l E (n + 1))))
    (K L : DerivedCategory (scalarReductionSource l E W)) :
    (scalarReductionDerivedExtension l E W n).obj (a.tensor.obj (K, L)) ≅
      b.tensor.obj ((scalarReductionDerivedExtension l E W n).obj K,
        (scalarReductionDerivedExtension l E W n).obj L) :=
  ((PurCompactSupport.finiteReductionIso l E W n).app _).symm ≪≫
    (PurCompactSupport.scalarTensor
      (PurCompactSupport.projection l E (n + 1) (Nat.succ_pos n) W) a b).app (K, L) ≪≫
    b.tensor.mapIso (Iso.prod ((PurCompactSupport.finiteReductionIso l E W n).app K)
      ((PurCompactSupport.finiteReductionIso l E W n).app L))

private noncomputable def reductionPullIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
      ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L) ≅
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj
      ((scalarReductionDerivedExtension l E Y n).obj L) := by
  let a := PurCompactSupport.reduction l E (n + 1) (Nat.succ_pos n)
  exact ((PurCompactSupport.finiteReductionIso l E X n).app _).symm ≪≫
    (PurCompactSupport.scalarPull a f).app L ≪≫
    (PurCompactSupport.pull (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) f).mapIso
      ((PurCompactSupport.finiteReductionIso l E Y n).app L)

private noncomputable def finiteSupportIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : proEtaleDerivedCategory X A) :
    (sfAmbientCompactSupportCandidate A c).obj K ≅
      (sfIntrinsicDerivedEquivalence Y A).functor.obj
        ((ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj
            ((sfIntrinsicDerivedEquivalence X A).inverse.obj K)) :=
  (sfAmbientCompactSupportCandidate A c).mapIso
    ((sfIntrinsicDerivedEquivalence X A).counitIso.app K).symm ≪≫
      (ProEtale.sfIntrinsicCompactSupportComparison A c).app
        ((sfIntrinsicDerivedEquivalence X A).inverse.obj K)

private noncomputable abbrev fixedDerived
    (A : Type u) [CommRing A] [Finite A] (W : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf (ProEt.topology W)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

-- Fix the small derived-category universe used by the published projection map.
private noncomputable abbrev fixedPull
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    @DerivedCategory.{u + 1, u + 1, u + 2} _ _ _ (fixedDerived A Y) ⥤
      @DerivedCategory.{u + 1, u + 1, u + 2} _ _ _ (fixedDerived A X) :=
  letI := fixedDerived A Y
  letI := fixedDerived A X
  (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor

private noncomputable def finitePullIso
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : proEtaleDerivedCategory Y A) :
    (proEtaleConstantRingDerivedPullback A f).obj L ≅
      (sfIntrinsicDerivedEquivalence X A).functor.obj
        ((fixedPull A f).obj ((sfIntrinsicDerivedEquivalence Y A).inverse.obj L)) :=
  (proEtaleConstantRingDerivedPullback A f).mapIso
    ((sfIntrinsicDerivedEquivalence Y A).counitIso.app L).symm ≪≫
      (finiteScalarPullbackComparison A f).app
        ((sfIntrinsicDerivedEquivalence Y A).inverse.obj L)

/-- Endpoint comparison data exists for arbitrary completed inputs.
Source: the proper/open scalar comparison and constant-scalar realization in
`lem-sf-ordinary-projection-reduction-arrow-comparison`.
(blueprint: lem-sf-ordinary-projection-endpoint-iso-data-q2). -/
theorem integralOrdinaryProjection_endpointIsoData
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X))
    (aZ : ProEtaleTensorModel c.Z ((PurCompactSupport.completed l E).ring c.Z))
    (aY : ProEtaleTensorModel Y ((PurCompactSupport.completed l E).ring Y))
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    Nonempty (IntegralOrdinaryProjectionEndpointData l E c aX aZ aY K L n) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨bX⟩ := PurCompactSupport.tensorModel_exists X (proEtaleConstantRing X A)
  obtain ⟨bY⟩ := PurCompactSupport.tensorModel_exists Y (proEtaleConstantRing Y A)
  let K₀ := (sfIntrinsicDerivedEquivalence X A).inverse.obj
    ((scalarReductionDerivedExtension l E X n).obj K)
  let L₀ := (sfIntrinsicDerivedEquivalence Y A).inverse.obj
    ((scalarReductionDerivedExtension l E Y n).obj L)
  let S := sfAmbientCompactSupportCandidate A c
  let H := aX.tensor.obj (K, (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L)
  let q := reductionImageIso l E c K n ≪≫
    finiteSupportIso A c ((scalarReductionDerivedExtension l E X n).obj K)
  let s := reductionTensorIso l E Y aY n bY
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K) L ≪≫
    bY.tensor.mapIso (Iso.prod q (Iso.refl _)) ≪≫
    bY.tensor.mapIso (Iso.prod (Iso.refl _)
      ((sfIntrinsicDerivedEquivalence Y A).counitIso.app
        ((scalarReductionDerivedExtension l E Y n).obj L)).symm) ≪≫
    (((finiteScalarTensorRealization Y A bY).app
      ((ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).obj K₀)).app L₀).symm
  let h := reductionTensorIso l E X aX n bX K
      ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L) ≪≫
    bX.tensor.mapIso (Iso.prod
      ((sfIntrinsicDerivedEquivalence X A).counitIso.app
        ((scalarReductionDerivedExtension l E X n).obj K)).symm
      (reductionPullIso l E f L n ≪≫
        finitePullIso A f ((scalarReductionDerivedExtension l E Y n).obj L))) ≪≫
    (((finiteScalarTensorRealization X A bX).app K₀).app
      ((fixedPull A f).obj L₀)).symm
  let t := reductionImageIso l E c H n ≪≫ S.mapIso h ≪≫
    (ProEtale.sfIntrinsicCompactSupportComparison A c).app
      (((ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj K₀).obj
        ((fixedPull A f).obj L₀))
  refine ⟨{ s := s, t := ?_ }⟩
  simpa only [H, A, K₀, L₀, fixedPull, PurCompactSupport.projectionMap,
    PurCompactSupport.tensorCurried, PurCompactSupport.image,
    SuppliedExchangeProjection.compactificationProjectionFromData,
    ProEtale.projectionMapOfCompactification, Arrow.mk_right, Functor.map_comp,
    ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj,
    Functor.comp_obj, Functor.postcompose₂_obj_obj_obj_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Functor.id_obj,
    Functor.curry_obj_obj_obj] using t

end WeilConjectures
