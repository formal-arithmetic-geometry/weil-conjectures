/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteScalarOrdinaryPullbackComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit

/-! # Factorized representative equation for finite scalar pullback

Source: Stacks Tags 07A6 and 0D6E.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors-factorized).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat
attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

/--
The factorized form of the representative equation.  It isolates the ordinary
termwise comparison and the two exact localization factors; the parent theorem
obtains the displayed left-derived counit form by the standard counit
factorization.  This is the derived mate calculation before that final rewrite.

Source: Stacks Tags 07A6 and 0D6E; the localization step in the proof of the
finite scalar inverse-mate representative formula.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors-factorized).
-/
theorem finiteScalarPullback_representative_factors_factorized
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (sfIntrinsicDerivedEquivalence X R).functor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R))
          p).leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P)) ≫
      (sfIntrinsicDerivedEquivalence X R).functor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R))
          p).mapDerivedCategoryFactors.hom.app P) ≫
      (sfIntrinsicModuleEquivalence X R).functor.mapDerivedCategoryFactors.hom.app
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((mapHomologicalComplexCompIso (finiteScalarOrdinaryPullbackComparison R p)
          (.up ℤ)).inv.app P) =
    (finiteScalarPullbackComparison R p).inv.app (DerivedCategory.Q.obj P) ≫
      (proEtaleConstantRingDerivedPullback R p).map
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app P) ≫
      (proEtaleRingDerivedPullbackFactors p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).hom.app
          (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

end WeilConjectures
