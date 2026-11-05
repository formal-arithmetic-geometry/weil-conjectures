/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.BundledTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorEvaluation
import all WeilConjectures.AlgebraicGeometry.System.SystemCochainTensorReduction
import all WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula

/-! # Composition of representative-normalized tensor comparisons

Source: Stacks 07A4, 06YS, 0G7E and 0G7D.
(blueprint: lem-coef-semilinear-tensor-comparison-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory

attribute [local irreducible] Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

end WeilConjectures.SemilinearSections
