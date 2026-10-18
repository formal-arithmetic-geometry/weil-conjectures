/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

/-! # Dimension of fibres in a fibre-component closure inside a flat family

Source: literature/stacks-project/more-morphisms.tex, Tag 0GSJ
(lemma-flat-associated-equidimensional), part (2), specialized to a fibre-component
generic point; Tag 0GSI (lemma-associated-point-specializes)
(blueprint: lem-trf-flat-fibre-component-closure-dimension).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Let `f : X ⟶ S` be flat and locally of finite type.  If `B` is an irreducible
component of the scheme-theoretic fibre over `t` and `y` is its generic point,
then every irreducible component `D` of the intersection of the closure of `y`
(in `X`) with the fibre over `s` has the same topological Krull dimension as `B`.
The proof has three steps.  First, the generic point of a component of the
locally Noetherian fibre is associated to its structure sheaf, hence is in the
relative assassin of `𝒪_X` (the fibre-component relative-associated lemma).
Second, apply the flat-associated-equidimensional lemma to `𝒪_X`; flatness of
`f` supplies its flatness hypothesis at every generic point of every fibre of
the reduced closure.  Third, the fibre of that closure over `t` has underlying
space `B`, and its fibres have the same underlying spaces as the displayed
intersections, so the relative dimension supplied by the lemma is
`topologicalKrullDim B` for every component `D`.  The empty intersection is
allowed because the component quantifier is then vacuous.
(blueprint: lem-trf-flat-fibre-component-closure-dimension).
-/
theorem flat_fibre_component_closure_dimension
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (t s : S) (B : Set (f.fiber t))
    (hB : B ∈ irreducibleComponents (f.fiber t))
    (y : f.fiber t) (hy : IsGenericPoint y B) :
    ∀ (D : Set
      (Set.inter (closure ({f.fiberι t y} : Set X)) ((f.base : X → S) ⁻¹' ({s} : Set S)))),
      D ∈ irreducibleComponents
        (Set.inter (closure ({f.fiberι t y} : Set X)) ((f.base : X → S) ⁻¹' ({s} : Set S))) →
      topologicalKrullDim D = topologicalKrullDim B := by
  sorry

end AlgebraicGeometry
