/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
import all WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

/-! # Derived canonical scalar pullback comparison

Source: the derived exact-functor composition and natural-isomorphism comparisons.
(auxiliary; not a blueprint node).
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
(auxiliary; not a blueprint node). -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  moduleAbelianForget Λ X

/-- Scalar forgetting is additive, section by section.
(auxiliary; not a blueprint node). -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive := moduleAbelianForget_additive Λ X

/-- Scalar forgetting preserves finite limits, as does its presheaf composite.
(auxiliary; not a blueprint node). -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := moduleAbelianForget_preservesFiniteLimits Λ X

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem.
(auxiliary; not a blueprint node). -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := moduleAbelianForget_preservesFiniteColimits Λ X

end AlgebraicGeometry.Etale.RawModuleScalarComparison
