/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-! # The normalized coefficient comparison before deriving

The coefficient functor, its tensor structure, and its pullback comparison are
constructed here. The remaining equality is a tensor equation on the abelian hearts.

Source: blueprint proper-base-change-finite, transport paragraph and clause (3).
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

attribute [local instance 20000] sheafBraidedCategory
-- Proof imports supply transported instances too; retain the native structure of the statement.
attribute [local instance 30000] CondensedRing.monoidal_upperStar
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

attribute [local irreducible] heartSectionsIso coefficientHeartEncoding
  coefficientHeartPushIso coefficientHeartPullIso

-- Retain the finite discrete hypotheses of the existing public statement.

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
