/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.PureDimension
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.RetrocompactBoundedFibreDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-! # The constructible high fibre-dimension locus contains every pure base change

Source: Stacks Project, Limits of Schemes, Tag 0EY2, lemma-descend-dimension-d,
proof, the open bounded-dimension locus and its constructible complement.
(blueprint: lem-trf-pure-base-change-constructible-image)

The locus `dim < d` expresses `dim ≤ d - 1` with subtraction in the integers.
Local dimension at a fibre point is nonnegative, so for `d = 0` this locus is empty.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The complement of the low fibre-dimension locus is constructible and contains
all points of any base change whose nonempty fibres have pure dimension `d`.
Both local fibre dimensions equal `d`, and every base-changed fibre has dimension at most `d`.

Source: Stacks Project, Limits of Schemes, Tag 0EY2, lemma-descend-dimension-d, proof;
Morphisms, Tags 02G0 and 02FY; Varieties, Tag 0A21; Topology, Tag 0B7I.
(blueprint: lem-trf-pure-base-change-constructible-image)

Proof:
1. At a fibre point every open neighbourhood is nonempty, so its dimension and the
   local dimension are nonnegative (def-kun-topological-dimension-at-point). Thus for
   `d = 0` the strict bounded-dimension locus is empty. For positive `d`, apply
   lem-trf-retrocompact-bounded-fibre-dimension with natural bound `d - 1` to obtain
   openness and retrocompactness. The strict bound equals the integer predecessor bound.
2. The complement is the single constructible piece `univ ∩ Uᶜ`, where `univ` and `U`
   are retrocompact opens (def-weil-constructible-subset). At `d = 0` it is `univ`.
3. Finite type includes locally finite type (def-weil-finite-type-morphism).
   Apply lem-weil-pbc-lft-base-change along `g`, then along each residue-field point.
   Thus every scheme-theoretic fibre (def-pc-scheme-fibre) of the new morphism is
   locally of finite type over its residue field.
4. The fibre containing any chosen point of the pullback is nonempty. Its pure
   dimension hypothesis (def-weil-pure-dimension) says each irreducible component has
   dimension `d`. Apply lem-sbc-equidimensional-open-local-dimension with the whole
   fibre as open subset to conclude that its local dimension at this point is `d`.
5. Apply lem-sc-fibre-dimension-after-base-change to identify that local dimension
   with the original fibre dimension at the first projection of the point. Both
   are `d`, so this projection cannot lie in the locus `dim < d`. This proves the
   equalities and the image containment.
6. By lem-weil-pbc-dimension-supremum-local-dimensions, the dimension of each new
   fibre is the supremum of its local dimensions, which step 4 bounds by `d`.
   For an empty fibre this is the empty supremum, bottom, also at most `d`. -/
theorem pure_base_change_constructible_image {X T : Scheme.{u}} (f : X ⟶ T)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFinitePresentation f] (d : ℕ) :
    IsOpen {x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)} ∧
    IsRetrocompact {x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)} ∧
    Topology.IsConstructible
      ({x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)}ᶜ) ∧
    (d = 0 →
      {x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)} = ∅ ∧
      {x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)}ᶜ = Set.univ) ∧
    (∀ (T' : Scheme.{u}) (g : T' ⟶ T),
      (∀ t' : T', Nonempty ((pullback.snd f g).fiber t') →
        ((pullback.snd f g).fiber t').IsPureDimension d) →
      (∀ x' : ↥(pullback f g),
        topologicalKrullDimAt ((pullback.snd f g).asFiber x') =
            topologicalKrullDimAt (f.asFiber (pullback.fst f g x')) ∧
          topologicalKrullDimAt (f.asFiber (pullback.fst f g x')) = (d : WithBot ℕ∞)) ∧
      Set.range (pullback.fst f g) ⊆
        {x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)}ᶜ ∧
      ∀ t' : T', topologicalKrullDim ((pullback.snd f g).fiber t') ≤ (d : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry
