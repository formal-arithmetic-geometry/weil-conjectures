/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
import all WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import Mathlib.RingTheory.AdicCompletion.Completeness
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.CategoryTheory.Exact.ExactScalarMatePasting

/-! # Constants and algebraic quotient restriction

Source: Stacks Tags 093J, 031C and 06YY.
(blueprint: lem-weil-pbc-constant-adic-quotient-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] CompletedConstantReduction.constant_additive

attribute [local instance] constant_limits constant_colimits
attribute [local irreducible] Functor.leftAdjoint
  ConstantScalarRealization.derivedExtension ConstantScalarRealization.moduleDerivedExtension
  ConstantScalarRealization.derivedAdjunction ConstantScalarRealization.moduleDerivedAdjunction
-- Completion evaluation identifies the actual power quotients.

-- Iterated mates exchange inverse-image and scalar adjunctions.

-- Keep this calculation abstract: none of the coefficient objects need to unfold.

-- Construct the section-normalized comparison from the three coefficient squares.

-- The other mate is the canonical invertible direct-image comparison.

-- Instantiate the abstract calculation without unfolding chosen adjoints.

end AlgebraicGeometry.Scheme
