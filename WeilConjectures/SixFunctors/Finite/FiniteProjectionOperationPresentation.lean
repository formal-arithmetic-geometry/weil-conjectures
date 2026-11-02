/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.SmoothPurity.Supporting.ProjectionFiniteReduction
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarProperProjectionPresentation

/-! # The finite projection in intrinsic tensor coordinates

Source: def-exchange-projection, the finite coefficient realization, and
prop-sf-pf-reduction, the specified finite projection map.
(blueprint: lem-sf-finite-projection-operation-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section FiniteReductionCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
open PurCompactSupport
open scoped CategoryTheory.Functor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The existing counit/open projection at the positive finite level, in intrinsic
constant-ring coordinates. The tensor presentations are the recorded normalized ones.
Source: blueprint prop-sf-pf-reduction, maps PF (blueprint: prop-sf-pf-reduction). -/
def finiteReductionProjection (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  ((projectionMap (finite l E (n + 1) (Nat.succ_pos n)) c
    (pullbackTensorFiniteModel l E X n) (pullbackTensorFiniteModel l E c.Z n)
    (pullbackTensorFiniteModel l E Y n)
    (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
      (Padic.coefficientExtensionRing l E (n + 1))).symm).app K).app L

end FiniteReductionCoordinates

private def arrowPostIso {A : Type*} [Category* A] {U V W : A}
    (f : U ⟶ V) (e : V ≅ W) : Arrow.mk f ≅ Arrow.mk (f ≫ e.hom) :=
  Arrow.isoMk (Iso.refl _) e (by simp)

private def mapArrowIso {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {f g : Arrow A} (e : f ≅ g) :
    Arrow.mk (F.map f.hom) ≅ Arrow.mk (F.map g.hom) :=
  F.mapArrow.mapIso e

private def bifunctorArrowIso {A B T : Type*} [Category* A] [Category* B] [Category* T]
    {P Q : A ⥤ B ⥤ T} (α : P ⟶ Q) {K K' : A} {L L' : B}
    (eK : K ≅ K') (eL : L ≅ L') :
    Arrow.mk ((α.app K).app L) ≅ Arrow.mk ((α.app K').app L') :=
  Arrow.isoMk (((P.mapIso eK).app L) ≪≫ (P.obj K').mapIso eL)
    (((Q.mapIso eK).app L) ≪≫ (Q.obj K').mapIso eL) (by
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Arrow.mk_hom]
      rw [Category.assoc, (α.app K').naturality, ← Category.assoc,
        NatTrans.naturality_app, Category.assoc])

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem fixedProperFactor
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [AlgebraicGeometry.ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    Nonempty (Arrow.mk
      (((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap A c.g).app
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory.obj K)).app
          L) ≅ Arrow.mk (projectionTensorCoordinateComponent A c K L)) := by
  let G := (AlgebraicGeometry.ProEtale.lowerStar A c.g).rightDerivedFunctor
  let J := (AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory
  let e := G.mapIso
    (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
      A c.i).app K).symm.app
      ((AlgebraicGeometry.ProEtale.upperStar A c.g).leftDerivedFunctor.obj L)) ≪≫
    G.mapIso (J.mapIso
      (((AlgebraicGeometry.ProEtale.derivedTensor A X).obj K).mapIso
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarCompactificationIso A c).app L)))
  let p := (((AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap A c.g).app
    (J.obj K)).app L)
  have h : Arrow.mk (projectionTensorCoordinateComponent A c K L) =
      Arrow.mk (p ≫ e.hom) := by
    simp only [projectionTensorCoordinateComponent,
      AlgebraicGeometry.ProEtale.projectionMapOfCompactification_app_app, e, J, G, p,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom]
    all_goals rfl
  exact ⟨arrowPostIso p e ≪≫ (eqToIso h).symm⟩

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private def finiteOpenRealizationIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E (m + 1))) :
    ((PurCompactSupport.openExtension
      (PurCompactSupport.finite l E (m + 1) (Nat.succ_pos m)) j).mapDerivedCategory).obj K ≅
    (sfIntrinsicDerivedEquivalence V (Padic.coefficientExtensionRing l E (m + 1))).functor.obj
      (((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (m + 1)))) j).mapDerivedCategory).obj
        ((sfIntrinsicDerivedEquivalence U
          (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj K)) := by
  let O := PurCompactSupport.openExtension
    (PurCompactSupport.finite l E (m + 1) (Nat.succ_pos m)) j
  let M := sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (m + 1))
  let e : O ≅ M := PurCompactSupport.finiteOpenIso l E m j
  letI : M.Additive :=
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).1
  letI : Limits.PreservesFiniteLimits M :=
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.1
  letI : Limits.PreservesFiniteColimits M :=
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.2
  have hAdd : M.Additive := inferInstance
  let ed := @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ O M
    inferInstance hAdd inferInstance inferInstance
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.1
    (sfIntrinsicExtensionByZero_exact j (Padic.coefficientExtensionRing l E (m + 1))).2.2 e
  exact ed.app K ≪≫
    (Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence U (Padic.coefficientExtensionRing l E (m + 1))).inverse
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (m + 1)))) j ⋙
        (sfIntrinsicModuleEquivalence V
          (Padic.coefficientExtensionRing l E (m + 1))).functor)).app K ≪≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)).app K

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  CategoryTheory.Functor.mapDerivedCategory

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem properToFixedCompactification
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aZ : ProEtaleTensorModel c.Z (proEtaleConstantRing c.Z R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (M : proEtaleDerivedCategory c.Z R) (K : proEtaleDerivedCategory X R)
    (L : proEtaleDerivedCategory Y R)
    (eJ : M ≅ (sfIntrinsicDerivedEquivalence c.Z R).functor.obj
      (((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) c.i).mapDerivedCategory).obj
        ((sfIntrinsicDerivedEquivalence X R).inverse.obj K))) :
    Nonempty (Arrow.mk (finiteScalarProperProjection R c.g aZ aY M L) ≅
      Arrow.mk ((sfIntrinsicDerivedEquivalence Y R).functor.map
        (projectionTensorCoordinateComponent (ModuleCat.{u + 1} (ULift.{u + 1} R)) c
          ((sfIntrinsicDerivedEquivalence X R).inverse.obj K)
          ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)))) := by
  let eK := (sfIntrinsicDerivedEquivalence c.Z R).inverse.mapIso eJ ≪≫
    ((sfIntrinsicDerivedEquivalence c.Z R).unitIso.app _).symm
  obtain ⟨h₂⟩ := finiteScalarProperProjection_presentation R c.g aZ aY M L
  let h₃ := mapArrowIso (sfIntrinsicDerivedEquivalence Y R).functor (bifunctorArrowIso
    (AlgebraicGeometry.ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) c.g) eK
    (Iso.refl ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)))
  obtain ⟨h₄⟩ := fixedProperFactor (ModuleCat.{u + 1} (ULift.{u + 1} R)) c
    ((sfIntrinsicDerivedEquivalence X R).inverse.obj K)
    ((sfIntrinsicDerivedEquivalence Y R).inverse.obj L)
  let h₅ := mapArrowIso (sfIntrinsicDerivedEquivalence Y R).functor h₄
  exact ⟨h₂ ≪≫ h₃ ≪≫ h₅⟩

end WeilConjectures
