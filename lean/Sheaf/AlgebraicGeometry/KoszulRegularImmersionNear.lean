/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.AlgebraicGeometry.LciCotangentPresentation

/-!
# Koszul regularity near a source point of an immersion

Source: Stacks Project, Divisors, Definition 31.21.1 (Tag 063J), Koszul-regular clause
(blueprint: def-sfb-koszul-regular-immersion-near).

The closed-chart predicate is the existing `CotangentPresentation.IsKoszulImmersion`.
The extra open source neighbourhood makes the condition local at the specified point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An immersion is Koszul-regular near `z` if its restriction to some open source
neighbourhood factors as a closed immersion into an open target subscheme, with
finite Koszul-regular generators locally near every point of that restricted source.
The closed-chart predicate allows varying lengths, including zero.
Source: Stacks Project, Divisors, Tag 063J, Koszul-regular clause
(blueprint: def-sfb-koszul-regular-immersion-near). -/
def IsKoszulRegularImmersionNear {Z P : Scheme.{u}} (i : Z ⟶ P) (z : Z) : Prop :=
  ∃ V : Z.Opens, z ∈ V ∧ ∃ U : P.Opens,
    ∃ j : V.toScheme ⟶ U.toScheme,
      IsClosedImmersion j ∧ j ≫ U.ι = V.ι ≫ i ∧
        CotangentPresentation.IsKoszulImmersion j

end AlgebraicGeometry
