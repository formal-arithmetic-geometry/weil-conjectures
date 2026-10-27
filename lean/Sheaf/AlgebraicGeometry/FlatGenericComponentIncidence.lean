/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Fibre components in closures of generic-fibre components

Source: Stacks Project, More on Morphisms, Tag 0GSK (remark-flat-equidimensional),
second list; the component-incidence argument uses Tags 03HV, 01K1, 01IS, 004W and 004V.
(blueprint: lem-trf-flat-generic-component-incidence)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A component of any fibre of a flat morphism to an integral scheme is a component
of the intersection of that fibre with the closure of a generic-fibre component.
The last equality identifies a component of the intersection subspace with the image
of the original component under the fibre inclusion.

Source: Stacks Project, Tag 0GSK (remark-flat-equidimensional), second list, with the
following component-incidence argument supplied by the DAG.
(blueprint: lem-trf-flat-generic-component-incidence)

Proof:
1. A fibre is a scheme, so sobriety (lem-sc-scheme-sober, Tag 01IS) gives a generic
   point of its closed irreducible component C (def-weil-irreducible-components).
   Fix any such point x. The fibre inclusion identifies the fibre homeomorphically
   with the inverse image of its base point (def-pc-scheme-fibre, Tag 01K1).
2. Since eta is generic (def-sc-generic-point), it generalizes s. Flatness lifts this
   generalization from the image of x to y over eta
   (lem-weil-pbc-flat-generalizations-lift, Tag 03HV, via going-down Tag 00HS).
3. Choose a component B of the generic fibre containing y
   (lem-sc-irreducible-components-cover, Tag 004W), and its generic point z by
   lem-sc-scheme-sober. The fibre embedding preserves specialization, so y belongs
   to the ambient closure of z. That closed set also contains x by transitivity.
4. Its intersection with the fibre over s is closed in that fibre, so it contains
   the closure C of x there. C remains irreducible in this intermediate subspace.
   Any larger irreducible subset of the intermediate subspace would be a larger
   irreducible subset of the whole fibre, contradicting maximality of C
   (def-weil-irreducible-components, Tag 004V). Thus C is a component there.
-/
theorem Flat.generic_fibre_component_incidence
    {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) [Flat f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (s : S) (C : Set (f.fiber s)) (hC : C ∈ irreducibleComponents (f.fiber s)) :
    (∃ x : f.fiber s, IsGenericPoint x C) ∧
      ∀ x : f.fiber s, IsGenericPoint x C →
        ∃ B : Set (f.fiber η), B ∈ irreducibleComponents (f.fiber η) ∧
          ∃ z : f.fiber η, IsGenericPoint z B ∧
            f.fiberι s x ∈ closure ({f.fiberι η z} : Set X) ∧
              ∃ D : Set (Set.inter (closure ({f.fiberι η z} : Set X)) (f ⁻¹' {s})),
                D ∈ irreducibleComponents
                  (Set.inter (closure ({f.fiberι η z} : Set X)) (f ⁻¹' {s})) ∧
                    Subtype.val '' D = (f.fiberι s) '' C := by
  sorry

end AlgebraicGeometry
