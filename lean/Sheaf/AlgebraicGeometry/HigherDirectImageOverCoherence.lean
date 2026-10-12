/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions

/-! # Functoriality of higher-image transitions

Source: Stacks Project, Tag 09Z1 and Tag 03Q8.
(blueprint: sbc-lem-higher-image-over-transition-coherence).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Canonical higher-image transitions are contravariantly functorial on schemes over W.
The maps are the canonical unit/composition/counit transitions of the source library.
Source: Stacks Project, Tag 09Z1, canonical comparison maps; Tag 03Q8.
(blueprint: sbc-lem-higher-image-over-transition-coherence).

Proof: Use the triangle identities for derived inverse/direct-image adjunctions to
cancel the unit and counit for an identity. For two composable arrows, expand both
units and counits using the composition adjunction. Naturality moves the intervening
unit past the counit, and the triangle identity cancels them. Associativity of the
inverse-image composition isomorphisms identifies the remaining factors with the
single transition for the composite. Apply homology and use the naturality and
composition coherence of inverse image on complexes concentrated in degree zero.
The final inverse-image identifications of G compose by upper-star coherence. -/
theorem higher_image_over_transition_coherence
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    : (∀ U : Over W, higherDirectImageOverMap Λ k G q (𝟙 U) = 𝟙 _) ∧
      (∀ {U V Z : Over W} (φ : U ⟶ V) (ψ : V ⟶ Z),
        higherDirectImageOverMap Λ k G q (φ ≫ ψ) =
          higherDirectImageOverMap Λ k G q ψ ≫ higherDirectImageOverMap Λ k G q φ) := by sorry

end AlgebraicGeometry.Etale
