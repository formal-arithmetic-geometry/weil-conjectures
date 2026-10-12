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

/-- The noetherian geometric argument produces an open stable locus agreeing with the
section component locus.
(blueprint: lem-sbc-smooth-section-component-noetherian-generalization-core) -/
theorem Smooth.exists_noetherian_section_component_stable_locus {P T : Scheme.{u}}
    (g : P ⟶ T) [Smooth g] [QuasiCompact g] [QuasiSeparated g]
    [IsNoetherian T]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    ∃ U : Set P, (∀ p, p ∈ U ↔ p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))) ∧
      StableUnderGeneralization U := by sorry

theorem Smooth.section_component_generalization_of_isNoetherian {P T : Scheme.{u}}
    (g : P ⟶ T) [Smooth g] [QuasiCompact g] [QuasiSeparated g] [IsNoetherian T]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) {x y : P} (hxy : y ⤳ x)
    (hx : x ∈ connectedComponentIn (g ⁻¹' {g x}) (σ (g x))) :
    y ∈ connectedComponentIn (g ⁻¹' {g y}) (σ (g y)) := by
  obtain ⟨U, hU, hstable⟩ := Smooth.exists_noetherian_section_component_stable_locus g σ hσ
  apply (hU y).mp
  apply hstable hxy
  exact (hU x).mpr hx

end AlgebraicGeometry
