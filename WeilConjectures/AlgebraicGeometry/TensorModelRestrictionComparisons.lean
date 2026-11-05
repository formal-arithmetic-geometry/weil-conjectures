/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.KFlatTensorModelNaturalComparison
import WeilConjectures.AlgebraicGeometry.DerivedTensorSymmetry
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence

/-! # Coherent tensor-model comparisons under open restriction

Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DL.
(blueprint: lem-sc-tensor-model-restriction-comparisons).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

end AlgebraicGeometry.Scheme
