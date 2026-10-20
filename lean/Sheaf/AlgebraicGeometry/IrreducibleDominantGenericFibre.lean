/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.Properties

/-!
# The generic fibre of a dominant morphism from an irreducible scheme

Source: Stacks Project, More on Morphisms, Tag 0G4F, passage to the generic fibre.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The fibre over a generic point of a dominant morphism with irreducible source is
irreducible. Reducedness, flatness and finite type are unnecessary.

Source: Stacks Project, More on Morphisms, Tag 0G4F, the generic-fibre passage in the proof.
(blueprint: lem-zl-irreducible-dominant-generic-fibre).

Proof: Dominance and continuity send the source generic point to the target generic point.
The topological fibre therefore contains the source generic point. Every two nonempty
relative opens in the fibre contain that point, proving irreducibility. The scheme fibre
is homeomorphic to this topological fibre. -/
theorem irreducibleSpace_fiber_of_isGenericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [IrreducibleSpace X] [IsDominant f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S)) :
    IrreducibleSpace (f.fiber η) := by
  have he : f (genericPoint X) = η := by
    apply IsGenericPoint.eq _ hη
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  rw [(f.fiberHomeo η).irreducibleSpace_iff, ← isIrreducible_iff_irreducibleSpace]
  refine ⟨⟨genericPoint X, he⟩, ?_⟩
  intro U V hU hV hFU hFV
  refine ⟨genericPoint X, he, ?_, ?_⟩
  · exact ((genericPoint_spec X).mem_open_set_iff hU).mpr
      ⟨hFU.choose, trivial, hFU.choose_spec.2⟩
  · exact ((genericPoint_spec X).mem_open_set_iff hV).mpr
      ⟨hFV.choose, trivial, hFV.choose_spec.2⟩

end AlgebraicGeometry
