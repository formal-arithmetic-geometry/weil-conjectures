/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Local noetherian models for a smooth section component

Source: Stacks Project, Tag 055Q.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Locally on the source, a smooth section component is the inverse image of the
component locus of a smooth section over a noetherian base.

Source: Stacks Project, Tag 055Q, first two paragraphs, and Tag 055M.
Proof: choose an affine neighbourhood V of g x and put W = g⁻¹(V). Restrict the section
and the smooth finitely presented morphism to V. Write the coordinate ring of V as a
filtered colimit of finite type Z-algebras. Descend the finitely presented morphism and
section to a stage, increasing the stage so that the section identity and smoothness
hold. This produces g₀ and σ₀ over a noetherian affine scheme T₀; quasi-compactness and
quasi-separatedness hold because the descended morphism is finitely presented. The
projection a from the base change W to P₀ is a scheme morphism. Restricting the base
has not changed any fibre or its section point. Tag 055M identifies the component locus
on the base change with the inverse image of the locus on P₀. Therefore the displayed
equivalence holds for every w, independently of any specialization or membership
assumption on x.

(blueprint: lem-sbc-smooth-section-component-noetherian-model) -/
theorem Smooth.exists_section_component_noetherian_model {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    (x : P) :
    ∃ (W : P.Opens) (_ : x ∈ W) (P₀ T₀ : Scheme.{u}) (g₀ : P₀ ⟶ T₀)
      (σ₀ : T₀ ⟶ P₀) (a : W.toScheme ⟶ P₀),
      IsNoetherian T₀ ∧ Smooth g₀ ∧ QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧
      σ₀ ≫ g₀ = 𝟙 T₀ ∧
      ∀ w : W.toScheme,
        (W.ι w ∈ connectedComponentIn (g ⁻¹' {g (W.ι w)}) (σ (g (W.ι w)))) ↔
          a w ∈ connectedComponentIn (g₀ ⁻¹' {g₀ (a w)}) (σ₀ (g₀ (a w))) := by sorry

end AlgebraicGeometry
