/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import WeilConjectures.AlgebraicGeometry.SchemeTensorUnitAction
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationTripleComponent
import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorUnitComponent
/-! # Ordinary evaluation: a step of the chain calculation
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- Prove tensor extensionality with abstract complexes, keeping coproduct data out of the
-- later component calculation on the concrete single-unit complex.

end AlgebraicGeometry
