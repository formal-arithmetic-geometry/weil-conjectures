/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Picard.DerivedTensorSecondFactorFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.DerivedCategory.Picard.MixedTensorPointwiseLeftDerived
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Derived tensor with a principal quotient is a multiplication cone

The chosen mixed derived tensor is compared with the two-term free coefficient resolution.
(blueprint: lem-pod-principal-derived-tensor-cone) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u wR wA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace DerivedCategory

end DerivedCategory
