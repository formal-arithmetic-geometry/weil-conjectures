/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent
import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality

/-! # Normalized derived tensor-Hom maps
Source: Stacks Project, cohomology.tex, Tag 08DJ, and sites-cohomology.tex, Tag 0A90.
(blueprint: lem-pc-canonical-derived-tensor-hom-map-existence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

end AlgebraicGeometry
