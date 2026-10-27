/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData

/-! Canonical identity normalization for Proj twisting sheaves.
Source: Stacks Project, constructions.tex, Tags 01MY and 01N2.
(blueprint: lem-sfb-proj-scalar-extension-twist-canonical-identity).

The proof expands the section-normalized tensor-pullback adjunction on the identity
scheme map. Its canonical identity comparison sends the normalized tensor section of
a homogeneous fraction to the original fraction. The denominator equation then gives
the required normalized scalar-extension formula pointwise on every open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The section-normalized identity pullback comparison obeys the identity fraction rule.
Source: Stacks Project, constructions.tex, Tags 01MY and 01N2.
(blueprint: lem-sfb-proj-scalar-extension-twist-canonical-identity).
-/
theorem scalarExtension_twist_canonical_identity
    {A : Type u} [CommRing A]
    {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] :
    IsScalarExtensionTwistComparison (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜))
      (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) := by
  sorry

end AlgebraicGeometry.Proj
