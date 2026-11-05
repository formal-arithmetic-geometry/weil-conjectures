/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import WeilConjectures.Algebra.Homology.HomComplexProjections
/-! # Degreewise ordinary evaluation and coefficient compatibility
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
-- A small component interface keeps the projection witness out of coproduct rewriting.

-- Evaluation into an arbitrary coefficient complex, defined by coproduct descent.

-- Inverse adjunction is natural in the coefficient; keep the projection abstract.

-- Descend the abstract component calculation before selecting any product witnesses.

end AlgebraicGeometry
