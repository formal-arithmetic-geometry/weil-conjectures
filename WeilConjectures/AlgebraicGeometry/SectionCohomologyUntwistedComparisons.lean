/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Untwisted comparison with raw section cohomology

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-section-cohomology-untwisted-comparisons).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] enoughInjectives

end AlgebraicGeometry.Scheme.Modules
