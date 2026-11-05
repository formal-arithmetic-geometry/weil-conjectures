/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientLiftKFlatResolution
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Derived scalar extension of the constant realization of an algebraic complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, and 0D6D;
sites-modules.tex, Tag 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local instance] ULift.algebra'
attribute [local irreducible] ConstantScalarRealization.moduleDerivedExtension
  ConstantScalarRealization.derivedExtension Functor.leftAdjoint

end AlgebraicGeometry.Scheme
