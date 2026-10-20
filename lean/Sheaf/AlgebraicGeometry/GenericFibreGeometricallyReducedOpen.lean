/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober

import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.AlgebraicGeometry.SchematicDensityGenericFibreOpen

/-!
# Geometrically reduced fibres near the generic fibre

Source: Stacks Project, More on Morphisms, Tag 0578,
`lemma-geometrically-reduced-generic-fibre`.
(blueprint: lem-trf-generic-fibre-geometrically-reduced-open)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite type morphism to an irreducible scheme with geometrically reduced generic
fibre has geometrically reduced fibres on a nonempty open of the base.

Source: Stacks Project, More on Morphisms, Tag 0578,
`lemma-geometrically-reduced-generic-fibre`.
(blueprint: lem-trf-generic-fibre-geometrically-reduced-open)

Proof:
1. Base change to the reduction of the base
   (lem-weil-pbc-reduction-universal-homeomorphism,
   def-weil-pbc-scheme-reduction). It is irreducible and reduced, hence integral
   (def-pc-integral-scheme). The reduction preserves residue fields and fibres
   (def-pc-scheme-fibre); finite type survives base change
   (lem-sfb-finite-type-composition-base-change). Nonempty opens correspond under
   the reduction homeomorphism. Restrict to a nonempty affine open of this base.
2. Generic flatness (lem-sbc-generic-flat-finite-presentation) gives a nonempty open
   on which the map is flat and locally finitely presented
   (def-sbc-locally-finite-presentation). Its generic fibre is unchanged, and its
   affine charts have the base-changed finite presentations
   (lem-weil-pbc-fibre-product-affine-spectra).
3. Each fibre is finite type over its residue field. A finite affine cover and
   lem-weil-pbc-finite-type-algebra-noetherian,
   lem-sc-affine-noetherian-underlying-space show that its space is Noetherian.
   Every subset is compact (lem-sfb-noetherian-space-compact-subsets), so every
   open immersion into a fibre is quasi-compact and quasi-separated.
4. Let U be the smooth locus of f. The smooth locus of the geometrically reduced
   generic fibre is dense (lem-pur-geometrically-reduced-dense-smooth-open).
   The flat pointwise fibre criterion (lem-trf-smooth-at-point-fibre-criterion)
   puts this locus inside the generic fibre of U. Every fibre of U is geometrically
   reduced (sbc-lem-smooth-geometrically-reduced), using the open-cover criterion
   lem-trf-reduced-scheme-open-cover after each field extension.
5. The generic fibre is reduced by the identity field extension in
   def-pc-geometrically-irreducible. Its dense open U is schematically dense by
   lemma-nagata-reduced-dense-image-schematic. The image-kernel description
   (def-nagata-scheme-theoretic-image) says its structure-sheaf map is injective.
6. Apply lem-trf-schematic-density-generic-fibre-open to obtain a nonempty open V
   of the base on every fibre of which U is schematically dense.
7. Fix y in V and an extension L of its residue field. On any affine fibre chart
   Spec D, base change is Spec of the tensor product
   (lem-weil-pbc-fibre-product-affine-spectra). The field-extension base change is
   faithfully flat (lem-weil-pbc-field-extension-base-change-faithfully-flat),
   hence its spectrum is flat (lem-weil-pbc-flat-ring-map-iff-flat-affine).
   Flat pullback preserves schematic density (lemma-nagata-dense-flat-pullback).
   The image-kernel description again gives an injective structure-sheaf map
   from this base-changed chart to its open coming from U, which is reduced.
8. A nilpotent section on that chart restricts to zero on the reduced open;
   injectivity forces it to be zero. The chart is reduced (def-pc-reduced-scheme).
   The charts cover the base-changed fibre, so lem-trf-reduced-scheme-open-cover
   makes it reduced. Since L was arbitrary this is geometric reducedness
   (def-pc-geometrically-irreducible). Transfer V through the earlier shrinks and
   reduction. Empty fibres satisfy the same reducedness and injectivity arguments. -/
theorem exists_nonempty_open_geometricallyReduced_fiber_of_generic
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IrreducibleSpace Y] (η : Y) (hη : IsGenericPoint η Set.univ)
    (hgeneric : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ y : Y, y ∈ V → GeometricallyReduced (f.fiberToSpecResidueField y) := by
  sorry

end AlgebraicGeometry
