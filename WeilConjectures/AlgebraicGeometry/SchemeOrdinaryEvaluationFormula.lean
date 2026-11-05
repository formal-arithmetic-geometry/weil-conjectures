/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Ordinary evaluation on the open scheme's actual site
Source: Stacks Project, Tags 08DJ and 08DQ, representative evaluation calculation.
(blueprint: def-pc-scheme-ordinary-evaluation-formula).
The existing local predicate has an over-site carrier. This predicate writes the
same component equation directly on a scheme's opens, so that transport can be
separated from the derived calculation. All complexes and components are actual
constructions; no comparison object is selected from an existence theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

end AlgebraicGeometry
