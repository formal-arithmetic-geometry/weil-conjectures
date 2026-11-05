/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Naturality of one tensor-Hom evaluation component

Source: Stacks Project, sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-tensor-hom-uncurry-component-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

-- Reassociate before applying a componentwise projection equation.

-- Naturality for any Hom complex, before choosing the scheme's resolution.

end AlgebraicGeometry
