/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Generalization of a smooth section component over a noetherian base

Source: Stacks Project, Tag 055Q.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The specialization step for a smooth section over a noetherian base.

Source: Stacks Project, Tag 055Q, noetherian and discrete valuation ring paragraphs,
using Tags 055M and 055J.
Proof: the source is noetherian because the morphism is finitely presented. If x = y,
there is nothing to prove. Otherwise a discrete valuation ring traces y ⤳ x (Tag 054F).
Base change to its spectrum. The tracing morphism supplies a second section τ, whose
special point maps to x and generic point to y. Tag 055M identifies the inverse image
of the component locus with the component locus of the base-changed section. Remove
from the special fibre the other components; they form a closed subset of the total
space, so their complement is open. Both sections factor through this open since their
special points lie in the chosen component. The special fibre is now connected. Pass
to the connected component of the total space containing the original section; it is
open and closed since the space is noetherian. It contains the entire connected special
fibre and therefore also the second section. Smoothness gives flatness and a reduced
special fibre, so Tag 055J makes its generic fibre connected. The two generic section
points belong to this connected fibre, and thus to the same component of the original
generic fibre. Tag 055M transports this membership back to y.

(blueprint: lem-sbc-smooth-section-component-noetherian-generalization) -/
theorem Smooth.section_component_generalization_of_isNoetherian {P T : Scheme.{u}}
    (g : P ⟶ T) [Smooth g] [QuasiCompact g] [QuasiSeparated g] [IsNoetherian T]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) {x y : P} (hxy : y ⤳ x)
    (hx : x ∈ connectedComponentIn (g ⁻¹' {g x}) (σ (g x))) :
    y ∈ connectedComponentIn (g ⁻¹' {g y}) (σ (g y)) := by sorry

end AlgebraicGeometry
