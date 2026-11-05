/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorShifts
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorModelIso
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorComparisonTransport
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness and first-variable shifts of the pro-etale projection mate

Source: Stacks Project, Cohomology on Sites, Tags 0B56 and 07A4;
Derived Categories, Tag 0A8D.
(blueprint: lem-sfb-proetale-projection-first-variable-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

open ProjectionRestriction

attribute [local implicit_reducible] resolving proEtaleFlatRepresentatives
  CategoryTheory.Functor.map₂HomologicalComplex Operation.left
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  HomologicalComplex₂.total MorphismProperty.Q'
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  proEtaleOrdinaryTensorPullback
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

end AlgebraicGeometry.Scheme.DerivedScalarMate
