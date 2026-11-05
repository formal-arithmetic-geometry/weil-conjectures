/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand

/-! # The differential identity for ordinary evaluation

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, ordinary complex comparison;
Section 20.41, the differential of the Hom complex.
(blueprint: lem-pc-ordinary-evaluation-differential).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

end AlgebraicGeometry
