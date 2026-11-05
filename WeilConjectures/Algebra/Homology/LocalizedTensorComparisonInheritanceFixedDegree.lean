/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonGenerators
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosure
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

-- STATEMENT-DISPUTED: the former single-degree hypothesis is false for shifted U.
-- For R=A=B=C=Z, Q=0, N=Z concentrated in degree 1, i=0 and U=Z
-- concentrated in degree -1, the hypothesis was 0 -> 0, but the conclusion is 0 -> Z.
-- The corrected helper requires the comparison for Q in every degree.

end ModuleCat
