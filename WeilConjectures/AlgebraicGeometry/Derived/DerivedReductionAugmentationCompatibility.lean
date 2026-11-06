/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonFormula
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Augmentation compatibility through computing reduction counits

The exact-square factor identity and normalized unit equations imply compatibility
of the derived comparison with augmentation, first on resolving complexes and then
on the derived category. These proved helpers support the stratum restriction proof.
Source: Stacks Tags 03EL, 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] completedReductionModuleTowerFunctor_additive
attribute [local irreducible] HasDerivedCategory.standard
  cochainRepresentativeWhiskering complexCounitNat
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
  completedReductionTower CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors CategoryTheory.Functor.mapDerivedCategoryFactorsh
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local irreducible] completedReductionModuleTowerFunctor
  completedReductionTowerComplexCounit reductionComplexCounit coherenceReductionTowerCounit

end AlgebraicGeometry.Scheme
