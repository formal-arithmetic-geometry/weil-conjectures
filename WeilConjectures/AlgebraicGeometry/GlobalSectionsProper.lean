/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-!
# Global functions on a proper scheme over a field

Let `X` be a proper scheme over a field `k`.

- If `X` is integral, then `Γ(X, 𝒪_X)` is a field, finite over `k`
  (`AlgebraicGeometry.Scheme.isField_globalSections_of_universallyClosed`,
  `AlgebraicGeometry.Scheme.finite_globalSectionsRingHom_of_isProper`).
- If `X` is geometrically integral, then `Γ(X, 𝒪_X) = k`
  (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral`).
- If `X` is geometrically reduced, then `Γ(X, 𝒪_X) = k` if and only if `X` is geometrically
  connected (`AlgebraicGeometry.Scheme.globalSectionsBijective_iff_geometricallyConnected`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

end AlgebraicGeometry.Scheme
