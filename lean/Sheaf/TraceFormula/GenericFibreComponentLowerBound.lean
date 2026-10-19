/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
import Mathlib.Topology.Baire.Lemmas
import Sheaf.AlgebraicGeometry.GenericClosedSubsetFibreNonempty
import Sheaf.AlgebraicGeometry.GenericFibreClosedCoverSpread
import Sheaf.AlgebraicGeometry.GenericOpenFibreDensity
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Lower bound for generic-fibre components

Source: Stacks Project, `literature/stacks-project/more-morphisms.tex`, Tag 0554
(`lemma-irreducible-components-in-neighbourhood`)
(blueprint: lem-trf-generic-fibre-component-lower-bound).
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory Topology
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
For a finite-type morphism over an irreducible base, the number of ordinary
irreducible components in the generic fibre is a lower bound for the fibres on
a nonempty open neighbourhood.

Proof (blueprint: lem-trf-generic-fibre-component-lower-bound):
1. If the generic component count is zero, take the whole base; otherwise enumerate
   the finitely many generic components and use their nonempty closed supports.
2. Take the closure of each generic component in the source and equip it with the
   reduced induced closed subscheme structure.  The fibre homeomorphism identifies
   its generic fibre with the original component and every other fibre with the
   corresponding closed subset of the fibre of the original morphism.
3. Each resulting closed-subscheme morphism is finite type, by the affine quotient
   description of a closed immersion.
4. For each pair of distinct components, apply generic open-fibre density to the
   complement of the other closure, obtaining a common neighbourhood where the
   pairwise complements are dense.
5. Apply generic-fibre closed-cover spreading to the finite union of all closures and
   the empty closed set, obtaining a neighbourhood on which they cover every fibre.
6. Apply generic closed-subset fibre nonemptiness to each closure, shrinking once more
   so that every closure has a nonempty fibre.
7. Intersect the finitely many neighbourhoods.  The finite dense-open intersection
   theorem gives, in each nonempty closure fibre, a point outside all other closures.
8. Put each selected point in an irreducible component of the fibre.  The finite closed
   covering forces that component into its selected closure, and the exclusive points
   show that the resulting components are distinct.
-/
theorem generic_fibre_component_lower_bound
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : IsIrreducible (Set.univ : Set Y))
    (η : Y) (hη : IsGenericPoint η (Set.univ : Set Y))
    (n : ℕ)
    (hn : Nonempty
      (({C : Set (f.fiber η) // C ∈ irreducibleComponents (f.fiber η)}) ≃ Fin n)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ t : Y, t ∈ V →
        ∃ ι : Fin n →
            {C : Set (f.fiber t) // C ∈ irreducibleComponents (f.fiber t)},
          Function.Injective ι := by
  sorry

end AlgebraicGeometry
