/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

/-! # Naturality of uncurrying on tensor summands
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local irreducible] homComplexFunctor
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local semireducible] homComplexFunctor

attribute [local irreducible] homComplexFunctor

end AlgebraicGeometry
