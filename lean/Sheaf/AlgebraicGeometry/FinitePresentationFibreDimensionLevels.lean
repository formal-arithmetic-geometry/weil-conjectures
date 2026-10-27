/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance
import Sheaf.TraceFormula.GenericFibreDimensionNeighborhood
import Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion

/-!
# Constructible fibre-dimension levels over a Noetherian base

Source: Stacks Project, More on Morphisms, Tag 05F9,
lemma-dimension-fibres-constructible, Noetherian-base paragraph.
(blueprint: lem-sfb-finite-presentation-fibre-dimension-levels).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The locus of fibres of any fixed finite nonnegative dimension is constructible
for a finitely presented morphism over a Noetherian scheme. Empty fibres have
Krull dimension bottom and belong to none of these loci, including the zero level.

Source: Stacks Project, More on Morphisms, Tag 05F9,
lemma-dimension-fibres-constructible, Noetherian-base paragraph.
(blueprint: lem-sfb-finite-presentation-fibre-dimension-levels).

Proof:
1. Local Noetherianity and quasi-compactness of `T` give a finite affine cover with
   Noetherian coordinate rings (`pqf-def-locnoeth`,
   `def-weil-pbc-quasi-compact-scheme`). Finite presentation implies finite type
   (`def-sbc-locally-finite-presentation`, `def-weil-finite-type-morphism`). Apply
   `lem-fin-finite-type-fibre-dimension-bound` to obtain a uniform natural bound;
   every nonempty fibre therefore has finite nonnegative dimension
   (`def-kun-topological-krull-dimension`).
2. Give a nonempty irreducible closed subset `Z` its reduced induced closed
   subscheme structure (`lem-weil-pbc-reduced-induced-closed-subscheme`) and choose
   its generic point `ξ` (`lem-weil-pbc-scheme-sober`). Base change to `Z` preserves
   finite presentation (`lem-weil-pbc-qcqs-morphism-permanence`). A point of a closed
   subscheme has the same residue field as its ambient point: on an affine chart
   both are the fraction field of `A / p` (`def-weil-residue-field`). The fibre-product
   universal property identifies each base-changed fibre with the original fibre,
   hence preserves its dimension (`def-pc-fibre-product`, `def-pc-scheme-fibre`).
3. If the generic fibre is empty, apply `lem-sbc-generic-fibre-closed-avoidance`
   to `h`, the point `ξ`, and the whole source. Intersect its open neighbourhood
   with the closure of `ξ`, which is `Z`. This gives a nonempty relatively open
   subset with only empty fibres. Its intersection with the dimension-`n` locus
   is empty because bottom is different from every natural dimension.
4. Otherwise the generic dimension is a natural number `m` by step 1. Apply
   `lem-trf-generic-fibre-dimension-neighborhood` to the base-changed morphism.
   On a nonempty open of `Z` all original fibres have dimension `m` by step 2.
   This open is contained in the level locus if `m = n`, and disjoint otherwise.
5. Thus every nonempty irreducible closed subset contains a nonempty relatively
   open subset either contained in or disjoint from the level locus. Apply
   `lem-trf-noetherian-constructible-subset-criterion`, using the finite affine
   Noetherian cover from step 1. For empty `T` the criterion is vacuous.
-/
theorem isConstructible_fibre_dimension_eq
    {Y T : Scheme.{u}} (h : Y ⟶ T) [IsLocallyNoetherian T] [CompactSpace T]
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h] (n : ℕ) :
    Topology.IsConstructible {t : T | topologicalKrullDim (h.fiber t) = (n : WithBot ℕ∞)} := by
  sorry

end AlgebraicGeometry
