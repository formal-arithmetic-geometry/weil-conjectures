/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalSectionsProper

/-!
# Global sections and geometric connectedness

Reference: Stacks Project, Tag 0FD2.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- For a proper geometrically reduced scheme over a field, the structure map on global
sections is bijective exactly when the scheme is geometrically connected. This is
`AlgebraicGeometry.Scheme.globalSectionsBijective_iff_geometricallyConnected` with the class
`GlobalSectionsBijective` unfolded (Stacks, Tag 0FD2). -/
theorem globalSectionsRingHom_bijective_iff_geometricallyConnected
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))] :
    Function.Bijective (globalSectionsRingHom k (X := X)) ↔
      GeometricallyConnected (X ↘ Spec (.of k)) :=
  ⟨fun h ↦ globalSectionsBijective_iff_geometricallyConnected.mp ⟨h⟩,
    fun h ↦ (globalSectionsBijective_iff_geometricallyConnected.mpr h).1⟩

end AlgebraicGeometry.Scheme
