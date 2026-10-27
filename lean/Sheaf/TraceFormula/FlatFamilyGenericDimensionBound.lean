/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.TraceFormula.FlatFibreComponentClosureDimension

/-! # A generic-fibre dimension bound for a flat family

Source: Stacks Project, Tag 0H3X (lemma-relative-dimension-support-flat), with the
structure sheaf, in literature/stacks-project/more-morphisms.tex
(blueprint: lem-trf-flat-family-generic-dimension-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every fibre of a flat locally finite type morphism over an integral scheme has
Krull dimension at most a given bound on its generic fibre. The nonnegative integer
bound is represented by `r : ℕ`. Empty fibres have dimension `⊥` and are included.

Source: Stacks Project, Tag 0H3X, applied to the structure sheaf
(blueprint: lem-trf-flat-family-generic-dimension-bound).

Proof:
1. Fix `s` and an irreducible component `C` of `f.fiber s`. By scheme sobriety
   (lem-sc-scheme-sober), choose its generic point `x`. The fibre embedding identifies
   it with a point of `Y`. Since `η` specializes to `s`, flat generalization lifting
   (lem-weil-pbc-flat-generalizations-lift) gives a point `y` over `η` specializing to `x`.
2. By lem-sc-irreducible-components-cover choose a component `B` of the generic fibre
   containing `y`, and by sobriety choose its generic point `z`. Then `z` specializes
   to `x` in `Y`. The intersection of the closure of `z` with the fibre over `s` is
   closed in that fibre and contains `C`. Maximality of `C` among irreducible subsets
   of the fibre makes `C` a component of this intersection as well.
3. Apply lem-trf-flat-fibre-component-closure-dimension to `B`, `z`, and `C` to get
   `dim C = dim B`. The subspace dimension inequality gives `dim B ≤ dim Y_η ≤ r`.
   This does not require flatness of the reduced closure of `z`.
4. Any finite strict chain of irreducible closed subsets of `f.fiber s` lies in a
   component by lem-sc-irreducible-components-cover applied to its largest member.
   The chain therefore has length at most `r`. Taking the supremum gives the bound.
   Empty fibres have no such chains, so their dimension is `⊥ ≤ r`. If the generic
   fibre is empty, step 1 forces every fibre to be empty.
-/
theorem fibre_dimension_le_of_generic_fibre_dimension_le
    {Y S : Scheme.{u}} [IsIntegral S] (f : Y ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (r : ℕ) (hgeneric : topologicalKrullDim (f.fiber η) ≤ (r : WithBot ℕ∞)) :
    ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (r : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
