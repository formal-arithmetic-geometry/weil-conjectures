/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.RestrictedScalarCohomologyLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteFreeApproximationHomology
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.AlgebraicGeometry.Restricted.RestrictedScalarCoefficientLocalConstancy
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteUnderlyingModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteActionLocalModels
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite scalar extension preserves constructible cohomology

Source: Stacks 06YY, 0944, and current scalar-extension clause (2), bpq #46.
(blueprint: lem-sp-finite-scalar-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u cv cu cw
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

attribute [-instance] proEtaleRingModules_hasDerivedCategory
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

end AlgebraicGeometry.Scheme
