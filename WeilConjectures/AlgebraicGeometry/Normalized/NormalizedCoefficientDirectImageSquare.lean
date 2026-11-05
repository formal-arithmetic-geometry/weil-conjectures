/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.CategoryTheory.Exact.ExactRestrictionDerivedIdentityUnit
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientDirectImageRestrictionCube

/-! # Compatibility of normalized direct-image squares with coefficient presentations

Source: Stacks Project, Cohomology on Sites, Tags 0D6D and 0D6E.
(blueprint: lem-pbc-normalized-coefficient-direct-image-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  proEtaleRingRestrictionDirectImage proEtaleRingRestrictionDerivedDirectImage
  pbcDerivedRestrictComp

end AlgebraicGeometry.Scheme
