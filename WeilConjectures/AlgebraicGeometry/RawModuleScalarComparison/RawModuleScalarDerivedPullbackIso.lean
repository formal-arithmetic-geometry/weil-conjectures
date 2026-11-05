/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

/-! # Derived canonical scalar pullback comparison

Source: the derived exact-functor composition and natural-isomorphism comparisons.
(blueprint: def-sbc-raw-scalar-derived-pullback-iso).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.RawModuleScalarComparison

end AlgebraicGeometry.Etale.RawModuleScalarComparison
