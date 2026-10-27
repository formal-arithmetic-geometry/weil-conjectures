/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import Sheaf.AlgebraicGeometry.SfP1ConstantUnitPullback
import Sheaf.AlgebraicGeometry.SfP1ConstantUnitHom

/-! # Ordinary finite inverse image and the single-degree unit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  derivedTensorUnit CategoryTheory.constantSheaf
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory DerivedCategory.singleFunctors
  upperStar lowerStar

/-- The specified finite-coefficient inverse image commutes with the native single-unit map.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, scalar integration normalization;
and thm-amb-p1-adjunction.proof.md, constant-unit normalization.
(blueprint: lem-pur-ordinary-finite-single-unit-pullback).

Proof: replace each native single-unit map by the proved constantUnit comparison.
The specified constantUnit_pullback equation then identifies the two composites.
Congruence with constantUnit_hom on the source and target supplies the two replacements.
-/
theorem ordinaryFiniteSingleUnitPullback_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (g : T ⟶ S) :
    (Etale.ordinaryFiniteUnitPullback A g).hom ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T).hom =
      (Etale.ordinaryFinitePullback A g).map
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom := by
  exact (congrArg (fun k ↦ (Etale.ordinaryFiniteUnitPullback A g).hom ≫ k)
      (Etale.SfP1Transport.constantUnit_hom A T).symm).trans
    ((Etale.SfP1Transport.constantUnit_pullback A g).trans
      (congrArg (fun k ↦ (Etale.ordinaryFinitePullback A g).map k ≫
          (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g).hom)
        (Etale.SfP1Transport.constantUnit_hom A S)))

end AlgebraicGeometry.Etale
