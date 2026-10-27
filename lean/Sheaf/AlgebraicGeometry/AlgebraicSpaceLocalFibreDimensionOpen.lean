/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen

/-!
# Bounded local fibre dimension for algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tags 04NM(3) and 04NT,
restricted to a scheme target (blueprint: lem-sfb-space-local-fibre-dimension-open).

An algebraic space `X` over `T` includes its structural morphism to the scheme `T`.
An étale scheme chart is `a : yoneda.obj U ⟶ X.obj.obj`, with `U : Over T`.
The scheme morphism `U.hom` is the composite of that chart with the structural map.

## Main definitions and statements

* `localFibreDimension`: the supremum specified in the node over affine étale charts.
* `localFibreDimension_chart_finite_isOpen`: chart independence, finiteness, and openness.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The local relative dimension is the supremum of the local topological dimensions of
scheme fibres at lifts in affine representable étale charts. For a chart point `v`,
`U.hom.asFiber v` is the unique point of the fibre over `U.hom v` mapping to `v`.
No choice of an atlas or field-valued representative is made.
Source: Stacks Project, Morphisms of Spaces, Tag 04NM(3), definition-dimension-fibre
(blueprint: lem-sfb-space-local-fibre-dimension-open). -/
noncomputable def localFibreDimension {T : Scheme.{u}} (X : AlgebraicSpace T)
    (x : Point X.obj.obj) : WithBot ℕ∞ :=
  ⨆ (U : Over T) (_ : IsAffine U.left) (a : yoneda.obj U ⟶ X.obj.obj)
    (_ : IsEtale a) (v : U.left) (_ : schemePointMap a v = x),
      topologicalKrullDimAt (U.hom.asFiber v)

/-- All affine étale charts compute the local relative dimension; it is a finite
nonnegative integer at every point, and every bounded-dimension source locus is open.
The only finite-type assumption is local finite type on étale scheme charts.
Source: Stacks Project, Morphisms of Spaces, Tags 04NM(3) and 04NT,
lemma-openness-bounded-dimension-fibres
(blueprint: lem-sfb-space-local-fibre-dimension-open).

Proof:
1. Choose an affine étale cover by `lem-a1-space-affine-etale-cover`. It lifts every
   point, so the chart family in the supremum is nonempty. Every chart map is open.
2. For two chart lifts of the same point, their fibre product is a scheme by
   `lem-trf-space-fibre-products-etale-covers`. By `lem-a1-space-fibre-product-point`
   it has a point above both lifts. The projections and their residue-field base
   changes are étale by `lem-trf-space-chartwise-etale-permanence`. The scheme fibre
   homeomorphisms (`def-pc-scheme-fibre`) identify the distinguished fibre points.
   Applying `lem-sfb-etale-topological-dimension-at-point` to both projections shows
   that the two chart dimensions agree. Their nonempty supremum equals every value.
3. By `lem-weil-pbc-lft-base-change`, a chart fibre is locally of finite type over its
   residue field. An affine neighbourhood of the distinguished point is finite type
   over that field. By `lem-kun-dimension-finite-type` it has finite dimension.
   Local dimension is at most that dimension and is nonnegative because every
   neighbourhood of the distinguished point is nonempty. Hence it is a natural number.
4. Apply `lem-weil-pbc-local-fibre-dimension-open` to every chart composite `U.hom`.
   By step 2 its open bounded-dimension locus is the inverse image of the locus in
   `X`. The latter is the union of the images of these open loci under the affine
   étale cover. These images are open by step 1, so their union is open. For an empty
   source the union is empty and the pointwise assertions are vacuous. -/
theorem localFibreDimension_chart_finite_isOpen {T : Scheme.{u}} (X : AlgebraicSpace T)
    (hft : ∀ (U : Over T) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom) :
    (∀ (x : Point X.obj.obj) (U : Over T) (a : yoneda.obj U ⟶ X.obj.obj),
      IsAffine U.left → IsEtale a → ∀ v : U.left, schemePointMap a v = x →
        topologicalKrullDimAt (U.hom.asFiber v) = localFibreDimension X x) ∧
    (∀ x : Point X.obj.obj, ∃ d : ℕ, localFibreDimension X x = (d : WithBot ℕ∞)) ∧
    (∀ d : ℕ, IsOpen {x : Point X.obj.obj | localFibreDimension X x ≤ (d : WithBot ℕ∞)}) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
