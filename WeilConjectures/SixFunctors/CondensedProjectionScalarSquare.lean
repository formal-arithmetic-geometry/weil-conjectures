/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.SixFunctors.ScalarSixCtf
public import WeilConjectures.SixFunctors.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.FiniteCohomologicalDimensionHypothesis
import Mathlib.Tactic.DefEqTransformations
import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
import WeilConjectures.AlgebraicGeometry.CondensedScalarProjectionCoherence
import WeilConjectures.AlgebraicGeometry.ScalarPullbackMateInverseNormalized
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! # The scalar square for the condensed compact-support projection

Source: Stacks Project, Tag 0E48, remark-compatible-with-diagram, with the
unit-normalized open-extension pasting; latest blueprint, sk-thm-sf-tensor-hom,
compatibility complement (blueprint: lem-sf-condensed-projection-scalar-square).

The projection is the published proper counit mate followed by the inverse open
unit mate and the derived pullback compositor. The scalar comparison is exactly
the published compact-support comparison, for each compactification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true


attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local implicit_reducible] moduleObjectDerivedPushforward

/-- The specified scalar/pullback isomorphism in the total left-derived presentation.
This is the recorded normalized comparison, conjugated only by the canonical
identification of exact termwise pullback with total derived pullback.
Source: det-prop-scalar-six-pullback (1), as used in the coefficient square of
Stacks Tag 0E48 (blueprint: lem-sf-condensed-projection-scalar-square). -/
def condensedScalarPullbackIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar Λ.X f).leftDerivedFunctor ⋙ scalarSixChange a X ≅
      scalarSixChange a Y ⋙ (upperStar Λ'.X f).leftDerivedFunctor :=
  Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ.X f)
      (scalarSixChange a X) ≪≫
    scalarDirectImagePullbackData.theta a f ≪≫
      Functor.isoWhiskerLeft (scalarSixChange a Y)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).symm

private lemma scalarPullbackComparison_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DiagonalCoefficients.scalarPullbackComparison (R := Λ.X) (T := Λ'.X) a.hom.hom f =
      (condensedScalarPullbackIso a f).hom := by
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y)
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  let t := (mateEquiv adjY adjX).symm
    (TwoSquare.mk _ _ _ _ (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)
  let eR := leftDerivedUpperStarIsoMapDerivedCategory Λ.X f
  let eS := (leftDerivedUpperStarIsoMapDerivedCategory Λ'.X f).symm
  have he : (t.whiskerTop eR.hom).whiskerBottom eS.hom =
      (mateEquiv adjY adjX).symm (TwoSquare.mk _ _ _ _
        (DiagonalCoefficients.scalarRestrictionPullbackIso
          (R := Λ.X) (T := Λ'.X) a.hom.hom f).inv) := by
    apply (mateEquiv adjY adjX).injective
    simp only [t, mateEquiv_whiskerTop_whiskerBottom, Equiv.apply_symm_apply]
    ext M
    dsimp only [eR, eS, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.mk, TwoSquare.natTrans]
    simp only [DiagonalCoefficients.scalarRestrictionPullbackIso,
      DiagonalCoefficients.derivedUpper,
      Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc, Equiv.apply_symm_apply]
  have h := congrArg TwoSquare.natTrans he
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
    TwoSquare.natTrans] at h
  simp only [t, adjY, adjX, eR, eS, DiagonalCoefficients.scalarPullbackComparison,
    Adjunction.pushHomOfComapIso, condensedScalarPullbackIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    scalarDirectImagePullbackData.thetaNormalization, scalarSixPullHom,
    TwoSquare.mk, TwoSquare.natTrans, Category.assoc,
    scalarSixChange, scalarSixAdjunctionLeft, scalarSixPull,
    DiagonalCoefficients.derivedUpper, DiagonalCoefficients.derivedScalars] at h ⊢
  convert h.symm using 2

private def scalarBalancingIso {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    QuotientChange.D (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y ⋙ QuotientChange.L Λ'.X f ≅
      QuotientChange.L Λ.X f ⋙
        QuotientChange.D (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X := by
  unfold QuotientChange.D QuotientChange.L
  exact (condensedScalarPullbackIso a f).symm

private lemma scalarBalancingIso_normalized {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    QuotientChange.PullNormalized (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f
      (scalarBalancingIso a f) := by
  obtain ⟨b, hb_inv, hb⟩ :=
    DiagonalCoefficients.scalar_pullback_mate_inverse_normalized
      (R := Λ.X) (T := Λ'.X) (a := a.hom.hom) (f := f)
  have he : b.symm = (scalarBalancingIso a f).symm := by
    apply Iso.ext
    change b.inv = (scalarBalancingIso a f).inv
    rw [hb_inv]
    have hh := scalarPullbackComparison_eq a f
    dsimp only [scalarBalancingIso, id, Iso.symm_inv]
    dsimp only [QuotientChange.D, QuotientChange.L, moduleObjectDerivedPullback,
      DiagonalCoefficients.derivedUpper, DiagonalCoefficients.derivedScalars] at hh ⊢
    delta QuotientChange.D QuotientChange.L moduleObjectDerivedPullback
    exact hh
  have he' : b = scalarBalancingIso a f := by
    simpa only [Iso.symm_symm_eq] using congrArg Iso.symm he
  rw [he'] at hb
  exact hb

private lemma scalarProjectionTensor_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u}) (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    QuotientChange.scalarProjectionTensor (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X K M =
      (by
        unfold QuotientChange.D
        exact (scalarSixTensorIso a X K M).hom) := by
  rfl

private lemma compactScalarProjection_eq
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ Y)) :
    QuotientChange.compactScalarProjection c K M =
      (by
        unfold QuotientChange.L moduleObjectDerivedPullback
        exact exceptionalProjectionMorphismOfCompactification Λ c K M) := by
  rfl

private lemma actualCompactScalarComparison_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    QuotientChange.actualCompactScalarComparison a c K =
      (by
        unfold QuotientChange.D
        exact (scalarCompactSupportMap a c.i c.g).app K) := by
  rfl

private lemma scalarBalancingIso_inv {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (scalarBalancingIso a f).inv = (by
      unfold QuotientChange.D QuotientChange.L moduleObjectDerivedPullback
      exact (condensedScalarPullbackIso a f).hom) := by
  rfl

private def scalarTensorAtOwn {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u}) (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a X).obj (K ⊗ M) ⟶
      (scalarSixChange a X).obj K ⊗ (scalarSixChange a X).obj M := by
  have v := QuotientChange.scalarProjectionTensor (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X K M
  beta_reduce at v
  delta QuotientChange.D QuotientChange.extension at v
  delta scalarSixChange scalarSixAdjunctionLeft
  exact v

private lemma scalarTensorAtOwn_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u}) (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    scalarTensorAtOwn a X K M = (scalarSixTensorIso a X K M).hom := by
  have h := scalarProjectionTensor_eq a X K M
  beta_reduce at h
  delta scalarTensorAtOwn
  beta_reduce
  delta QuotientChange.D QuotientChange.extension scalarSixChange scalarSixAdjunctionLeft id
    at h ⊢
  beta_reduce
  exact h

private def scalarCompactAtOwn {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarSixChange a Y).obj ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K) ⟶
      (rightDerivedLowerShriekOfCompactification Λ'.X c).obj ((scalarSixChange a X).obj K) := by
  have v := QuotientChange.actualCompactScalarComparison a c K
  beta_reduce at v
  delta QuotientChange.D QuotientChange.extension at v
  delta scalarSixChange scalarSixAdjunctionLeft
  exact v

private lemma scalarCompactAtOwn_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    scalarCompactAtOwn a c K = (scalarCompactSupportMap a c.i c.g).app K := by
  have h := actualCompactScalarComparison_eq a c K
  beta_reduce at h
  delta scalarCompactAtOwn
  beta_reduce
  delta QuotientChange.D QuotientChange.extension scalarSixChange scalarSixAdjunctionLeft id
    RootCoordinateFace.lower moduleObjectDerivedPushforward at h ⊢
  exact h

private def compactProjectionAtOwn
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ Y)) :
    (rightDerivedLowerShriekOfCompactification Λ c).obj K ⊗ M ⟶
      (rightDerivedLowerShriekOfCompactification Λ c).obj
        (K ⊗ (upperStar Λ f).leftDerivedFunctor.obj M) := by
  have v := QuotientChange.compactScalarProjection (Λ := Λ) c K M
  beta_reduce at v
  delta QuotientChange.L moduleObjectDerivedPullback at v
  exact v

private lemma compactProjectionAtOwn_eq
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ Y)) :
    compactProjectionAtOwn Λ c K M =
      exceptionalProjectionMorphismOfCompactification Λ c K M := by
  have h := compactScalarProjection_eq (Λ := Λ) c K M
  beta_reduce at h
  delta compactProjectionAtOwn
  delta QuotientChange.L moduleObjectDerivedPullback id at h ⊢
  exact h

private lemma tensorWhiskerPath_congr {C : Type*} [Category C] [MonoidalCategory C]
    {P Q Q' N Z : C} {d d' : P ⟶ Q ⊗ N} {q q' : Q ⟶ Q'}
    {p p' : Q' ⊗ N ⟶ Z} (hd : d = d') (hq : q = q') (hp : p = p') :
    d' ≫ q' ▷ N ≫ p' = d ≫ (q ⊗ₘ 𝟙 N) ≫ p := by
  rw [hd, hq, hp, MonoidalCategory.tensorHom_id]

set_option maxHeartbeats 400000 in
-- The kernel checks the specified derived functor endpoints.
private def ambientProjectionScalarLeft {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a Y).obj
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K ⊗ M) ⟶
      (rightDerivedLowerShriekOfCompactification Λ'.X c).obj
        ((scalarSixChange a X).obj K ⊗
          (upperStar Λ'.X f).leftDerivedFunctor.obj ((scalarSixChange a Y).obj M)) :=
  scalarTensorAtOwn a Y ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K) M ≫
    (scalarCompactAtOwn a c K ⊗ₘ 𝟙 ((scalarSixChange a Y).obj M)) ≫
    compactProjectionAtOwn Λ'.X c ((scalarSixChange a X).obj K)
      ((scalarSixChange a Y).obj M)

set_option maxHeartbeats 400000 in
-- The kernel checks the specified derived functor endpoints.
private def ambientProjectionScalarRight {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a Y).obj
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K ⊗ M) ⟶
      (rightDerivedLowerShriekOfCompactification Λ'.X c).obj
        ((scalarSixChange a X).obj K ⊗
          (upperStar Λ'.X f).leftDerivedFunctor.obj ((scalarSixChange a Y).obj M)) := by
  have v :=
    (QuotientChange.D (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y).map
        (QuotientChange.compactScalarProjection (Λ := Λ.X) c K M) ≫
      QuotientChange.actualCompactScalarComparison a c
        (K ⊗ (QuotientChange.L Λ.X f).obj M) ≫
      (rightDerivedLowerShriekOfCompactification Λ'.X c).map
        (QuotientChange.scalarProjectionTensor (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X K
          ((QuotientChange.L Λ.X f).obj M)) ≫
      (rightDerivedLowerShriekOfCompactification Λ'.X c).map
        (𝟙 ((QuotientChange.D (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X).obj K) ⊗ₘ
          (scalarBalancingIso a f).inv.app M)
  beta_reduce at v
  delta QuotientChange.D QuotientChange.L moduleObjectDerivedPullback
    QuotientChange.extension at v
  delta scalarSixChange scalarSixAdjunctionLeft
  exact v

set_option maxHeartbeats 400000 in
-- The kernel checks the specified derived functor endpoints.
private lemma ambientProjectionScalarSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X.left))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y.left)) :
    ambientProjectionScalarLeft a c K M = ambientProjectionScalarRight a c K M := by
  have h := QuotientChange.condensedScalarCompactProjectionCoherence
    (ell := ell) (k := k) (_hcd := _hcd) (a := a) (_ha := _ha)
    (A := Λ) (B := Λ') (X := X) (Y := Y) (f := f) (c := c)
    (b := scalarBalancingIso a f.left) (_hb := scalarBalancingIso_normalized a f.left)
    (K := K) (N := M)
  beta_reduce at h
  delta ambientProjectionScalarLeft ambientProjectionScalarRight scalarTensorAtOwn
    scalarCompactAtOwn compactProjectionAtOwn
  beta_reduce
  delta QuotientChange.D QuotientChange.L moduleObjectDerivedPullback
    QuotientChange.extension scalarSixChange scalarSixAdjunctionLeft id at h ⊢
  beta_reduce
  exact h

set_option maxHeartbeats 400000 in
-- The kernel checks the specified derived functor endpoints.
private lemma projectionScalarLeft_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixTensorIso a Y
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K) M).hom ≫
      ((scalarCompactSupportMap a c.i c.g).app K ▷ (scalarSixChange a Y).obj M) ≫
      exceptionalProjectionMorphismOfCompactification Λ'.X c
        ((scalarSixChange a X).obj K) ((scalarSixChange a Y).obj M) =
      ambientProjectionScalarLeft a c K M := by
  have hd := scalarTensorAtOwn_eq a Y
    ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K) M
  have hq := scalarCompactAtOwn_eq a c K
  have hp := compactProjectionAtOwn_eq (Λ := Λ'.X) c
    ((scalarSixChange a X).obj K) ((scalarSixChange a Y).obj M)
  beta_reduce at hd hq hp
  unfold ambientProjectionScalarLeft
  exact tensorWhiskerPath_congr
    (C := DerivedCategory (ModuleRingedComparison.internalModules Λ'.X Y))
    (P := (scalarSixChange a Y).obj
      ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K ⊗ M))
    (Q := (scalarSixChange a Y).obj
      ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K))
    (Q' := (rightDerivedLowerShriekOfCompactification Λ'.X c).obj
      ((scalarSixChange a X).obj K))
    (N := (scalarSixChange a Y).obj M)
    (Z := (rightDerivedLowerShriekOfCompactification Λ'.X c).obj
      ((scalarSixChange a X).obj K ⊗
        (upperStar Λ'.X f).leftDerivedFunctor.obj ((scalarSixChange a Y).obj M)))
    hd hq hp

set_option maxHeartbeats 400000 in
-- The kernel checks the specified derived functor endpoints.
private lemma projectionScalarRight_eq {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :
    (scalarSixChange a Y).map
        (exceptionalProjectionMorphismOfCompactification Λ.X c K M) ≫
      (scalarCompactSupportMap a c.i c.g).app
        (K ⊗ (upperStar Λ.X f).leftDerivedFunctor.obj M) ≫
      (rightDerivedLowerShriekOfCompactification Λ'.X c).map
        ((scalarSixTensorIso a X K ((upperStar Λ.X f).leftDerivedFunctor.obj M)).hom ≫
          ((scalarSixChange a X).obj K ◁ (condensedScalarPullbackIso a f).hom.app M)) =
      ambientProjectionScalarRight a c K M := by
  delta ambientProjectionScalarRight
  beta_reduce
  simp only [scalarProjectionTensor_eq, actualCompactScalarComparison_eq,
    compactScalarProjection_eq, scalarBalancingIso_inv]
  beta_reduce
  delta QuotientChange.D QuotientChange.L moduleObjectDerivedPullback
    QuotientChange.extension scalarSixChange scalarSixAdjunctionLeft id
  beta_reduce
  simp only [MonoidalCategory.id_tensorHom, ← Functor.map_comp]

set_option maxHeartbeats 400000 in
-- The kernel checks the specified derived functor endpoints.
/-- Derived scalar extension commutes with the specified compact-support projection.
Composition is written in Lean's left-to-right order. Both sides start at
T_Y(F K tensor L) and finish at F'(T_X K tensor Lf'^* T_Y L).
Source: Stacks Project, Tag 0E48, remark-compatible-with-diagram, with the
normalized open-extension refinement; latest blueprint sk-thm-sf-tensor-hom,
compatibility complement (blueprint: lem-sf-condensed-projection-scalar-square).

Proof:
1. Apply the existing compact-support clause of
lem-fix-condensed-scalar-projection-coherence to the ambient objects K.obj and
L.obj and the given compactification.
2. Obtain its normalized pullback isomorphism from
lem-sfb-scalar-pullback-mate-inverse-normalized. Its inverse is the specified
scalar-adjunction mate. Mates commute with whiskering, so transporting the exact
restriction square along the canonical exact-to-derived pullback isomorphisms
identifies that inverse with condensedScalarPullbackIso. The theta normalization
of lem-sfb-scalar-direct-image-mate-coherence fixes exactly the same mate.
3. Identify both scalar tensor maps with the same forward monoidal tensorator.
Expand the compact-support interface wrappers, rewrite tensoring with identities
as whiskering, and combine the successive functor maps. This gives the displayed
equality without inverting a projection or direct-image comparison. -/
theorem condensedProjectionScalarSquare
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (_hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ell k)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y.left) :
    (scalarSixTensorIso a Y.left
        ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K.obj) L.obj).hom ≫
      ((scalarCompactSupportMap a c.i c.g).app K.obj ▷
        (scalarSixChange a Y.left).obj L.obj) ≫
      exceptionalProjectionMorphismOfCompactification Λ'.X c
        ((scalarSixChange a X.left).obj K.obj) ((scalarSixChange a Y.left).obj L.obj) =
    (scalarSixChange a Y.left).map
        (exceptionalProjectionMorphismOfCompactification Λ.X c K.obj L.obj) ≫
      (scalarCompactSupportMap a c.i c.g).app
        (K.obj ⊗ (upperStar Λ.X f.left).leftDerivedFunctor.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification Λ'.X c).map
        ((scalarSixTensorIso a X.left K.obj
          ((upperStar Λ.X f.left).leftDerivedFunctor.obj L.obj)).hom ≫
          ((scalarSixChange a X.left).obj K.obj ◁
            (condensedScalarPullbackIso a f.left).hom.app L.obj)) := by
  exact (projectionScalarLeft_eq a c K.obj L.obj).trans
    ((ambientProjectionScalarSquare ell k _hcd a _ha f c K.obj L.obj).trans
      (projectionScalarRight_eq a c K.obj L.obj).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
