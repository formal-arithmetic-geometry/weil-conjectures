/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.SfP1IntegralTransportData
import Sheaf.AlgebraicGeometry.SfP1ConstantUnitNormalization

/-! # Normalization of the constant-object right unitor -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale.SfP1Transport
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local instance 2000] Abelian.toPreadditive

/-- The right unitor based on the actual constant object.
(blueprint: lem-sf-p1-cached-right-unit-normalization) -/
def cachedRightUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    ((ordinaryFiniteTensor A S).obj K).obj (ordinaryFiniteUnit A S) ≅ K :=
  ((ordinaryFiniteTensor A S).obj K).mapIso (constantUnit A S) ≪≫
    derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K

/-- Identifying the constant object identifies its right unitor.

Source: constantUnit_eq_single and the definition of derivedTensorSingleUnitIso.
Proof: compare inverse components, then apply functoriality to the equality of unit
isomorphisms. This works for every complex, including zero, over every scheme.
(blueprint: lem-sf-p1-cached-right-unit-normalization) -/
theorem cachedRightUnit_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    cachedRightUnit A S K = derivedTensorSingleUnitIso K := by
  apply Iso.ext_inv
  dsimp only [cachedRightUnit, derivedTensorSingleUnitIso, Iso.trans_inv, Functor.mapIso_inv]
  exact congrArg
    (fun r ↦ (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).inv ≫
      ((ordinaryFiniteTensor A S).obj K).map r)
    (congrArg Iso.inv (constantUnit_eq_single A S))

end AlgebraicGeometry.Etale.SfP1Transport
