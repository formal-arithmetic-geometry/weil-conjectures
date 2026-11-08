/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientChange.CoefficientOperationComparisons
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Canonical coefficient comparisons for the six-functor transformations

Source: the adopted `AlgebraicGeometry.coefficientChangeCompatibility` docstring and fields.
The latest blueprint `lem-fix-operation-reduction` supplies the route on its narrower stages.
-/

@[expose] public section
set_option autoImplicit false
universe u

-- Normalize quotient coefficient instances as in IntegralCoefficients.
attribute [local instance 2000] CommRing.toRing
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.CoefficientChange

set_option hygiene false in
local notation "DE(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} A))
set_option hygiene false in
local notation "DP(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

end AlgebraicGeometry.CoefficientChange
