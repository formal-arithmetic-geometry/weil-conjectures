/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Scalar compatibility for a support Hom factor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The open factor of the canonical support Hom map, with ordinary pullback.
Source: scalar Hom generator, open tensor-Hom adjunction.
(blueprint: lem-sfb-scalar-open-support-hom-square). -/
def scalarSixOpenSupportHomMap (Λ : ScalarSixRing.{u})
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X U))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)) :
    (ihom ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.obj P)).obj N ⟶
      (lowerStar Λ.X j).rightDerivedFunctor.obj
        ((ihom P).obj ((scalarSixPull Λ j).obj N)) :=
  openSupportHomMap Λ.X j P N ≫
    (lowerStar Λ.X j).rightDerivedFunctor.map
      ((ihom P).map
        ((Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ.X j)).hom.app N))

set_option maxHeartbeats 1600000 in
-- The statement includes the derived coefficient-transport comparisons.
end AlgebraicGeometry.ProEtale.CondensedRing
