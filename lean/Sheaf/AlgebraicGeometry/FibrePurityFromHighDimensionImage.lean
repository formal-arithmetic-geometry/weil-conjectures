/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange

/-! # Fibre purity from an image in the high fibre-dimension locus

Source: Stacks Project, Tag 0EY2, proof of lemma-descend-dimension-d, final sentence;
Tags 02FY and 0B1B supply the local-dimension and component arguments
(blueprint: lem-trf-fibre-purity-from-high-dimension-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- If the fibres of a finite type morphism have dimension at most `d`, and the image of
an arbitrary base change lies in the locus of local fibre dimension at least `d`, both
local fibre dimensions at every point of the base change equal `d`, and every nonempty
base-changed fibre is pure of dimension `d`. Thus all of its irreducible components have
Krull dimension `d`. Empty sources and fibres are allowed.

Source: Stacks Project, Tag 0EY2, proof of lemma-descend-dimension-d, final sentence,
with Tags 02FY (part (1)) and 0B1B (dimensions of components through a point).
(blueprint: lem-trf-fibre-purity-from-high-dimension-image)

Proof:
1. Fix a point `x'` of the pullback, with image `x` in `X`. Finite type implies locally
   finite type. Apply lem-sc-fibre-dimension-after-base-change to identify the local fibre
   dimensions at `x'` and `x`. The image containment makes the latter at least `d`.
   The whole fibre is an open neighbourhood of its point `f.asFiber x`, so the infimum
   defining topologicalKrullDimAt is at most the dimension of that fibre, hence at most
   `d` by the upper bound. Antisymmetry gives the two asserted equalities.
2. Fix `t'`. The same base-change lemma identifies the fibre over `t'` with the residue
   field extension of the fibre over `g t'`. The latter is locally of finite type over
   its residue field by def-pc-scheme-fibre and lem-weil-pbc-lft-base-change. Apply
   lem-trf-field-extension-component-local-dimension: each irreducible component of
   the extended fibre has a generic point, and its dimension is the local topological
   dimension there. Step 1 makes this `d`. This is def-weil-pure-dimension, including
   its assertion about every irreducible component. Empty fibres have no components;
   an empty source has no points to check. None of these steps restricts `g`.
-/
theorem fibre_purity_from_high_dimension_image
    {X T T' : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hupper : ∀ t : T, topologicalKrullDim (f.fiber t) ≤ (d : WithBot ℕ∞))
    (g : T' ⟶ T)
    (himage : Set.range (pullback.fst f g) ⊆
      {x : X | (d : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x)}) :
    (∀ x' : ↥(pullback f g),
      topologicalKrullDimAt ((pullback.snd f g).asFiber x') =
          topologicalKrullDimAt (f.asFiber (pullback.fst f g x')) ∧
        topologicalKrullDimAt (f.asFiber (pullback.fst f g x')) = (d : WithBot ℕ∞)) ∧
    (∀ t' : T', Nonempty ((pullback.snd f g).fiber t') →
      ((pullback.snd f g).fiber t').IsPureDimension d) := by
  sorry

end AlgebraicGeometry
