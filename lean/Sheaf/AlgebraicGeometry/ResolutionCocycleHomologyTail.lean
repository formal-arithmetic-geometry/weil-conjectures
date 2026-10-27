/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedResolutionCocycle

/-! # The shifted resolution homology composite

Source: Stacks Project, Tags 072W and 0DVC.
(blueprint: def-weil-pbc-resolution-cocycle-homology-tail).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

/-- The explicit shift and inverse classical resolution comparisons.
Source: Stacks Project, Tags 072W and 0DVC, computation of right derived functors
on an injective resolution and compatibility of its homology with shifts.
(blueprint: def-weil-pbc-resolution-cocycle-homology-tail).

First apply zeroth homology to the termwise direct-image shift comparison, then
shift homology to degree q, and finally apply the two prescribed inverse classical
resolution comparisons. All four factors are the existing constructed maps.
The declared source uses the bounded-below shifted resolution, so consumers can
compose this map without expanding the degreewise data of the shifted complex. -/
@[irreducible] noncomputable def resolutionCocycleHomologyTail
    {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution F) :
    (((lowerStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex (.up ℤ)).obj
      (normalizationShiftedResolution F I q).obj).homology 0 ⟶
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  let R := lowerStar AddCommGrpCat.{u + 1} f
  HomologicalComplex.homologyMap
      (((R.mapHomologicalComplex (.up ℤ)).commShiftIso (q : ℤ)).hom.app
        I.cochainComplex) 0 ≫
    ((HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) ≫
    (I.isoRightDerivedObjCochainComplex R q).inv ≫
    (R.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).inv

end AlgebraicGeometry.Etale
