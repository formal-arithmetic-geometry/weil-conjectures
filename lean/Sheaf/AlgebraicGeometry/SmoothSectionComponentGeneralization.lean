/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Generalization stability of a smooth section component

Source: Stacks Project, Tag 055Q, generic-point argument.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The relative connected component of a smooth section is stable under generalization.

Source: Stacks Project, Tag 055Q, specifically its generic-point argument.
Proof: smoothness supplies flatness and geometrically reduced fibres. Work locally on the
base and descend the finite-presentation morphism and section to a noetherian model,
retaining flatness. The component containing the rational section point commutes with
base change by Tag 055M. For a specialization from x' to x with x in the section component,
choose a trait mapping its generic and special points to x' and x. After base change,
remove the other special-fibre components. The remaining special fibre is connected.
Restrict further to the connected component of the total space containing the section;
it contains the whole special fibre. Tag 055J makes its generic fibre connected, since
the family is flat and the special fibre is geometrically reduced. The trait's second
section through x and x' consequently has its generic point in the component selected
by the original section. Its image x' is in the required locus. Base-change compatibility
returns the conclusion on the original scheme.

(blueprint: lem-sbc-smooth-section-component-generalization) -/
theorem Smooth.stableUnderGeneralization_section_component {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    StableUnderGeneralization
      {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  sorry

end AlgebraicGeometry
