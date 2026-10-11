/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Open and closed pieces of smooth proper schemes

Source: Stacks Project, Morphisms, Tags 01VC, 01VA, 01W5 and 01W3
(blueprint: lem-pc-clopen-smooth-proper-curve).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An open and closed immersion into a smooth proper scheme over a field has a smooth
proper composite structure morphism. Source: Stacks Project, Morphisms, Tags 01VC, 01VA,
01W5 and 01W3 (blueprint: lem-pc-clopen-smooth-proper-curve).

Proof:
1. Since `i` is an open immersion, it is smooth by Tag 01VC. Composing it with the smooth
   structure morphism `f` gives a smooth morphism by Tag 01VA, as in
   `lem-pc-open-immersion-smooth-composition`.
2. Since `i` is a closed immersion, it is proper by Tag 01W5. Its composite with the proper
   structure morphism `f` is proper by Tag 01W3, as in clause (b) of
   `lem-weil-pbc-closed-immersion-proper`. -/
theorem smooth_and_isProper_of_clopen_immersion
    {K : Type u} [Field K] {Y Z : Scheme.{u}} [Nonempty Z]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [IsProper f]
    (i : Z ⟶ Y) [IsOpenImmersion i] [IsClosedImmersion i] :
    Smooth (i ≫ f) ∧ IsProper (i ≫ f) := by
  sorry

end AlgebraicGeometry
