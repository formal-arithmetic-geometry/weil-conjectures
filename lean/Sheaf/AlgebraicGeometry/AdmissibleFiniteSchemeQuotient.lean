/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Topology.Maps.Basic

/-!
# Admissible finite scheme quotients

Source: ILO, Travaux de Gabber, Expose IX, 1.4, pp. 132--133, the admissible scheme
quotients used in situation (*) (blueprint: def-per-admissible-finite-scheme-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite scheme quotient of an admissible action has the orbit quotient topology and
invariant structure sheaf. Invariance of a section is expressed on every open contained in
both its domain and the inverse image of that domain under the action. This compares the
actual pullback and restriction maps, without choosing identifications of equal opens.
Source: ILO, Expose IX, 1.4, pp. 132--133
(blueprint: def-per-admissible-finite-scheme-quotient). -/
def IsAdmissibleFiniteSchemeQuotient {G : Type v} [Group G] [Finite G]
    {C X : Scheme.{u}} (a : G →* Aut C) (π : C ⟶ X) : Prop :=
  (∀ c : C, ∃ U : C.affineOpens, ∀ g : G, (a g).hom c ∈ U.1) ∧
  IsFinite π ∧
  (∀ g : G, (a g).hom ≫ π = π) ∧
  Topology.IsQuotientMap π ∧
  (∀ c d : C, π c = π d ↔ ∃ g : G, (a g).hom c = d) ∧
  ∀ U : X.Opens,
    Function.Injective (π.app U).hom ∧
    ∀ s : Γ(C, π ⁻¹ᵁ U),
      (s ∈ Set.range (π.app U).hom ↔
        ∀ (g : G) (W : C.Opens) (hW : W ≤ π ⁻¹ᵁ U)
          (hWg : W ≤ (a g).hom ⁻¹ᵁ (π ⁻¹ᵁ U)),
          ((a g).hom.appLE (π ⁻¹ᵁ U) W hWg).hom s =
            (C.presheaf.map (homOfLE hW).op).hom s)

end AlgebraicGeometry
