/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import Mathlib.Topology.JacobsonSpace

/-!
# Finite maps from proper schemes of dimension at most one

Source: Stacks Project, Curves, Tag 0CCL, lemma-finite
(blueprint: lem-sfb-proper-dimension-one-noncontraction-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism from a proper scheme of dimension at most one over a field to a separated
scheme over that field is finite if every one-dimensional irreducible component has at
least two image points.

Source: Stacks Project, Curves, Tag 0CCL, lemma-finite
(blueprint: lem-sfb-proper-dimension-one-noncontraction-finite).

Proof:
1. By [lem-weil-pbc-proper-over-separated], the morphism `f` is proper because its
composition with the separated structure morphism of `Y` is the proper structure morphism
of `X`. Its image is closed and images of closed points are closed by
[def-weil-proper-morphism].
2. Properness gives finite type over `k` by [def-weil-proper-morphism] and
[def-weil-finite-type-morphism]. A finite affine cover has Noetherian coordinate rings by
[lem-wf-affine-noetherian-components]. Thus `X` and its topology are Noetherian.
3. If `y` is the image of a closed point, its fibre is closed. A strict chain of two
nonempty irreducible closed subsets `A < B` in that fibre would force `B` to be an
irreducible component of `X`: a further strict enlargement would contradict dimension at
most one. Then `B` has dimension one and singleton image, contradicting noncontraction.
Thus this fibre has dimension at most zero, using [def-kun-topological-krull-dimension]
and [def-weil-irreducible-components].
4. By [lem-sc-noetherian-closed-subset-finite-components] the fibre is a finite union of
irreducible closed subsets. By [lem-weil-pbc-scheme-sober] each has a unique generic point.
Dimension at most zero forces each subset to consist of its generic point: any other
point has a nonempty irreducible closure, which must equal the whole subset and would
give a second generic point. Hence the fibre is finite.
5. By [lem-trf-proper-finite-fibre-finite-near], `f` is finite above an open neighbourhood
of every such `y`, without any Noetherian hypothesis on `Y`.
6. The union `U` of these neighbourhoods contains the image of `X`. Otherwise its inverse
image complement is a nonempty closed subset of `X` and contains a closed point by
[lem-sc-lft-over-field-jacobson-space], a contradiction. Thus `U` and the complement of
the closed image of `X` cover `Y`.
7. On affine opens refining this cover, inverse images are affine: use finiteness above
`U`, and the empty affine scheme off the image. By [pqf-lem-affine-local-target], `f` is
affine. It is proper by step 1, so [lem-sfb-affine-proper-finite] makes it finite.
-/
theorem isFinite_of_proper_dim_le_one_noncontraction
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (h_dim : topologicalKrullDim X ≤ 1)
    (h_noncontraction : ∀ Z : Set X, Z ∈ irreducibleComponents X →
      topologicalKrullDim Z = 1 → (f '' Z).Nontrivial) :
    IsFinite f := by
  sorry

end AlgebraicGeometry
