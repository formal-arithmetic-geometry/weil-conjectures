/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Local constructibility of the component selected by a section

Source: Stacks Project, Tag 055P.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The relative connected component of a section is locally constructible.

Source: Stacks Project, Tag 055P, with base-change compatibility from Tag 055M.
Proof: work over an affine open of the base. Finite presentation descends the morphism
and section to a finite type Z-algebra. The component of a rational section point is
geometrically connected, so the locus commutes with base change. On the noetherian model,
consider any irreducible closed subset Z of the source, with generic point x and image y.
Tag 055N supplies a nonempty open V in the closure of y on which the section component
is clopen. Put W = Z intersected with the inverse image of V, a nonempty open of Z.
Since W is irreducible, its intersection with the component locus is empty or all of W.
Thus the locus in Z is not dense or contains a nonempty open. The noetherian
constructibility criterion proves constructibility. Pulling back proves local
constructibility. Quasi-compactness and quasi-separatedness make local finite
presentation into finite presentation, as required for this descent.

(blueprint: lem-sbc-section-component-locally-constructible) -/
theorem isLocallyConstructible_section_component {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    IsLocallyConstructible {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  sorry

end AlgebraicGeometry
