/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Local noetherian models for the component selected by a section

Source: Stacks Project, Tag 055P, first reduction, and Tag 055M.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Near each source point, the section component is the inverse image of the section
component of a finitely presented morphism between noetherian schemes.

Source: Stacks Project, Tag 055P, first reduction, using Tags 01ZM and 055M.
Proof: choose an affine neighbourhood V of g(p) and put U = g inverse image V.
The restriction of g to U is finitely presented, since g is locally finitely presented,
quasi-compact and quasi-separated. Write the coordinate ring of V as the filtered union
of its finitely generated Z-subalgebras. Finite-presentation descent (01ZM) descends the
restricted morphism, its section and the section identity to a finite stage. Let T0 be
that affine stage and P0 its finitely presented source. Both are noetherian, since T0 is
of finite type over Z and P0 is of finite type over T0. The projection rho from the base
change to P0 is a scheme morphism. The section component commutes with this base change
by 055M: the connected component of the rational section point is geometrically connected,
so its base change is contained in the new component, while the continuous image of the
new component is connected and contains the original section point, giving the reverse
inclusion. Restriction to V does not change the fibres or their section points. This
identifies the original component on U with the displayed inverse image.

(blueprint: lem-sbc-section-component-noetherian-model) -/
theorem exists_section_component_noetherian_model {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (p : P) :
    ∃ (U : P.Opens), p ∈ U ∧ ∃ (P₀ T₀ : Scheme.{u}) (g₀ : P₀ ⟶ T₀)
      (σ₀ : T₀ ⟶ P₀) (ρ : U.toScheme ⟶ P₀),
      IsNoetherian P₀ ∧ IsNoetherian T₀ ∧ LocallyOfFinitePresentation g₀ ∧
      QuasiCompact g₀ ∧ QuasiSeparated g₀ ∧ σ₀ ≫ g₀ = 𝟙 T₀ ∧
      U.ι ⁻¹' {q : P | q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q))} =
        ρ ⁻¹' {q : P₀ | q ∈ connectedComponentIn (g₀ ⁻¹' {g₀ q}) (σ₀ (g₀ q))} := by
  sorry

end AlgebraicGeometry
