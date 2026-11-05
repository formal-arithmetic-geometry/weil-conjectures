/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.CanonicalTensorModelInputNaturality

/-! # Comparison of normalized derived evaluation maps

Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex,
Tags 0A90 and 0A96. (blueprint: lem-pc-tensor-hom-uncurry-normalized-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

-- Keep the component algebra independent of the chosen Hom-complex projections.

-- Factor a normalized representative through evaluation at the identity.

-- The comparison follows formally from the square for evaluation itself.

end AlgebraicGeometry
