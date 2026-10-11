/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-!
# Global sections and geometric connectedness

Source: Stacks Project, Varieties, Lemma 0FD2; blueprint
`lem-pc-h0-geom-connected` (blueprint: lem-pc-h0-geom-connected).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- For a proper geometrically reduced scheme over a field, the structure map on global
sections is bijective exactly when the scheme is geometrically connected (Stacks, Tag 0FD2;
blueprint: lem-pc-h0-geom-connected). (blueprint: lem-pc-h0-geom-connected)

First, properness and coherence of the structure sheaf make the global sections finite over
the field. Flat base change identifies their scalar extension to any field extension with
the global sections after base change. A scheme is nonempty exactly when its global-sections
ring is nonzero. If the structure map is bijective, every such base change has a field as
its global-sections ring, hence is nonempty and connected by the idempotent criterion.
Conversely, after extension to an algebraic closure the global-sections ring is finite,
reduced, nonzero, and has no nontrivial idempotents. It therefore has dimension one over
the algebraic closure; flat base change gives dimension one over the original field, so
the structure map is bijective. -/
theorem globalSectionsRingHom_bijective_iff_geometricallyConnected
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))] :
    Function.Bijective (globalSectionsRingHom k (X := X)) ↔
      GeometricallyConnected (X ↘ Spec (.of k)) := by
  sorry

end AlgebraicGeometry.Scheme
