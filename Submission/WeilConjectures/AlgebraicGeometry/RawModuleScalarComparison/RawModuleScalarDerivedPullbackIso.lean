/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all Submission.WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- Forget scalar operations on a module sheaf.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  moduleAbelianForget Λ X

/-- Scalar forgetting is additive, section by section.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive := moduleAbelianForget_additive Λ X

/-- Scalar forgetting preserves finite limits, as does its presheaf composite.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := moduleAbelianForget_preservesFiniteLimits Λ X

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem.
(blueprint: def-sbc-raw-module-scalar-pullback-comparison). -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := moduleAbelianForget_preservesFiniteColimits Λ X

end AlgebraicGeometry.Etale.RawModuleScalarComparison
