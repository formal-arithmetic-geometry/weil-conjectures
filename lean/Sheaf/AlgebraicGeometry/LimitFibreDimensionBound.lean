/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.LimitAffineTransition

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBound
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Fibre dimension bounds descend to a finite stage

Source: Stacks Project, Limits, Tag 05M5, lemma-limit-dimension
(blueprint: lem-trf-limit-fibre-dimension-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical comparison from the `j`-th source to the base change of the `i`-th
source along the transition `Sⱼ ⟶ Sᵢ`.
Source: Stacks Project, Limits, Tag 05M5, lemma-limit-dimension
(blueprint: lem-trf-limit-fibre-dimension-bound). -/
noncomputable def limitFibreComparison {I : Type u} [Preorder I]
    {S X : Iᵒᵖ ⥤ Scheme.{u}} (τ : X ⟶ S) {i j : I} (hij : i ≤ j) :
    X.obj (op j) ⟶
      pullback (τ.app (op i)) (S.map (homOfLE hij).op) :=
  pullback.lift (X.map (homOfLE hij).op) (τ.app (op j)) (τ.naturality (homOfLE hij).op)

/-- The morphism between two limit cones induced by a natural transformation of diagrams.
Source: Stacks Project, Limits, Tag 05M5, lemma-limit-dimension
(blueprint: lem-trf-limit-fibre-dimension-bound). -/
noncomputable def limitFibreMap {I : Type u} [Preorder I]
    {S X : Iᵒᵖ ⥤ Scheme.{u}} (τ : X ⟶ S)
    (cS : Cone S) (hcS : IsLimit cS) (cX : Cone X) : cX.pt ⟶ cS.pt :=
  hcS.lift ((Cone.postcompose τ).obj cX)

/-- If a limit of finite-type morphisms with affine transitions has all fibres of dimension at
most `d`, then the same bound holds for every fibre at some finite stage.

Source: Stacks Project, Limits, Tag 05M5, lemma-limit-dimension
(blueprint: lem-trf-limit-fibre-dimension-bound).

Proof, following the node's seven steps:
1. Choose an index and pass to its cofinal directed tail: compatible cones extend to the whole
   index set by taking common upper bounds, so the limits do not change. Choose a finite affine
   cover of this base stage and finite affine covers of the preimages under its finite-type
   morphism, using lem-pqf-finite-affine-cover-qc-open. Pull these covers back at every later stage.
2. The base charts are affine by hSaff. Each source chart is a closed subscheme of the base
   change of its initial affine chart, hence affine, by
   lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-fibre-product-affine-spectra and
   lem-weil-pbc-closed-immersion-affine-cover-criterion. The restricted comparison is again a
   closed immersion by base change. By lem-weil-pbc-lft-affine-pairs the coordinate ring maps
   are finite type, and the base-change comparison maps of rings are surjective.
3. By the pullback universal property, each chart of the limit is the limit of its chart
   system: compatible maps give a map to the whole limit factoring through the initial open.
   The inverse construction uses its projections. By lem-weil-pbc-limit-affine-transition
   these chart limits are spectra of the corresponding filtered colimits of rings.
4. Each limit chart fibre is an open subscheme of the corresponding fibre of the whole limit,
   by lem-weil-pbc-open-immersion-base-change. Its dimension is at most d: apply
   lem-weil-pbc-dimension-at-point-open-subspace and
   lem-weil-pbc-dimension-supremum-local-dimensions to hdim. The affine fibre-product theorem
   expresses these fibres as spectra of residue-field tensor products.
5. Apply lem-weil-pbc-affine-limit-fibre-dimension-bound to every chart, using the finite-type
   and surjectivity properties of Step 2 and the colimit descriptions of Step 3. Each chart
   acquires a stage where all its fibres have dimension at most d.
6. Such bounds persist at later stages: base change the closed comparison to a residue field.
   The later fibre is closed in the field extension of the earlier one. The latter has the
   same local fibre dimensions by lem-sc-fibre-dimension-after-base-change; closed subspaces
   have no larger local dimension, by intersecting open neighbourhoods and comparing chains
   of irreducible closed subsets. Take the supremum of local dimensions.
7. Take a common upper bound of the finitely many chart stages. Every point of any fibre at
   this stage lies in a chart fibre, an open neighbourhood with the same local dimension.
   The supremum-of-local-dimensions theorem gives the global bound. If the source cover is
   empty, the initial source is empty and that stage already works. Empty bases and fibres
   cause no exception, since their dimension is bottom. -/
theorem limit_fibre_dimension_bound
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (S X : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (S.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (S.obj (op i))]
    (τ : X ⟶ S)
    (hSaff : ∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (S.map (homOfLE hij).op))
    (hfinite : ∀ i : I,
      LocallyOfFiniteType (τ.app (op i)) ∧ QuasiCompact (τ.app (op i)))
    (hclosed : ∀ {i j : I} (hij : i ≤ j),
      IsClosedImmersion (limitFibreComparison τ hij))
    (cS : Cone S) (hcS : IsLimit cS)
    (cX : Cone X) (hcX : IsLimit cX)
    (d : ℕ)
    (hdim : ∀ s : cS.pt,
      topologicalKrullDim ((limitFibreMap τ cS hcS cX).fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ s : S.obj (op i),
      topologicalKrullDim ((τ.app (op i)).fiber s) ≤ (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
