/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.KrullDimension

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound

/-!
# Fibre and image dimension bounds over a field

Source: Stacks Project, `varieties.tex`, Tag 0B2L,
`lemma-dimension-fibres-locally-algebraic`, (2)(a) and its proof, applied to the finitely
many irreducible components (blueprint: lem-zl-finite-type-fibre-image-dimension-bounds).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, `varieties.tex`, Tag 0B2L,
`lemma-dimension-fibres-locally-algebraic`, (2)(a) and proof
(blueprint: lem-zl-finite-type-fibre-image-dimension-bounds).

For a morphism of finite-type schemes over a field, the closure of the image has dimension
at most that of the source. If the target has dimension at most `d` and all scheme-theoretic
fibres have dimension at most `n`, then the source has dimension at most `d + n`.
All dimensions are topological Krull dimensions, with the empty space having dimension `⊥`.

Proof (the four node steps).
1. The empty source has empty image, so both bounds are immediate. Otherwise finite type
   over the Noetherian field makes the source Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`), with finitely many irreducible components
   (`lem-sc-noetherian-finite-irreducible-components`). All relevant finite-type dimensions
   are finite (`lem-kun-dimension-finite-type`).
2. Give each component its reduced closed-subscheme structure
   (`lem-weil-pbc-closed-subset-closed-subscheme`). Closed immersions are finite and locally
   of finite type (`lem-weil-pbc-closed-immersion-finite`,
   `lem-weil-pbc-immersion-base-change-lft`), so composition makes the component finite type
   over the field (`lem-sfb-finite-type-composition-base-change`). For its restricted map,
   put `Zᵢ` equal to its image closure and `rᵢ = dim Xᵢ - dim Zᵢ`. The dense open equality
   locus of `lem-zl-irreducible-fibre-dimension-lower-bound` has a point; local fibre
   dimension there is nonnegative (`def-kun-topological-dimension-at-point`), so `rᵢ ≥ 0`.
3. The image closure is the finite union of the `Zᵢ`. Every irreducible closed subset of
   that union lies in one member, so its dimension is at most the maximum of their
   dimensions. Step 2 bounds this maximum by the maximum of the component dimensions,
   which equals the dimension of the source.
4. At the generic point of each component the same lower-bound lemma gives
   `rᵢ ≤ dim_ηᵢ (Xᵢ)ᵧᵢ`. The component fibre is a closed subscheme of the whole fibre by
   `lem-pc-closed-imm-base-change`; `def-pc-scheme-fibre` identifies the underlying spaces.
   Intersecting open neighbourhoods with this closed subspace and comparing irreducible
   chains gives local dimension at most that of the ambient fibre, hence at most `n`.
   Also `dim Zᵢ ≤ dim Y ≤ d`. Thus `dim Xᵢ ≤ d + n`; taking the maximum proves the bound.
-/
theorem Scheme.Hom.finiteType_fibre_image_dimension_bounds
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    topologicalKrullDim (closure (Set.range f)) ≤ topologicalKrullDim X ∧
      ∀ (d n : ℕ), topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
        (∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (n : WithBot ℕ∞)) →
        topologicalKrullDim X ≤ ((d + n : ℕ) : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
