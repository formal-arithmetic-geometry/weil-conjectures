/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # Differential compatibility of componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-differential).
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

-- The signed chain-map equation transported through the additive tensor-Hom adjunction.

-- Mathlib's total differential restricted to one tensor summand, with its exact sign.

-- Work with abstract projections so rewrites do not unfold their existence specification.

-- Specialize to the fixed Hom-complex projections, using the small projection API.
-- Its choice is definitionally the original choice, by proof irrelevance.

end AlgebraicGeometry
