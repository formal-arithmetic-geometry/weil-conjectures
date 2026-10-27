/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.TraceFormula.SchematicallyDenseOpen

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Schematic generic density of the smooth open

Source: Stacks Project, Tag 0578, proof paragraph 2; Tags 056V, 01V9 and 056D
(blueprint: lem-trf-smooth-open-schematic-generic-density).

The open `f.smoothLocus` is the union of the opens on which `f` is smooth:
`Scheme.Hom.preimage_smoothLocus_eq` and `Scheme.Hom.smoothLocus_eq_top_iff`
identify smooth restrictions with opens contained in this locus.
Its fibre at `y` is represented by the inverse-image open under `f.fiberι y`,
with structure map its inclusion followed by `f.fiberToSpecResidueField y`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The smooth open has dense and schematically dense generic fibre, finite-type
Noetherian ambient fibres whose open immersions are quasi-compact and quasi-separated,
and geometrically reduced fibres of its own. Empty fibres are permitted.

Source: Stacks Project, Tag 0578, second proof paragraph; Tags 056V, 01V9 and 056D
(blueprint: lem-trf-smooth-open-schematic-generic-density).

Proof plan:
1. Finite type is stable under base change
   (`lem-sfb-finite-type-composition-base-change`). Each residue field is Noetherian,
   so `lem-weil-pbc-finite-type-over-noetherian` makes each fibre Noetherian.
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` gives the descending-chain
   condition. Open immersions into the fibres are quasi-compact by
   `lem-sfb-noetherian-open-immersion-qc` and separated, hence quasi-separated, by
   `lem-weil-pbc-separated-cancellation`. Local finite presentation of the fibre
   structure maps also follows from `pqf-lem-lft-fp-locnoeth`.
2. The smooth restrictions cover the smooth open, so its structure map is smooth
   by `lem-weil-pbc-smooth-local-on-source`, including when that open is empty.
3. `lem-pur-geometrically-reduced-dense-smooth-open` gives a dense smooth locus in
   the generic fibre. By `lem-trf-flat-fibre-smooth-locus-image`, every point in
   that locus maps into `f.smoothLocus`, proving density of its inverse image.
4. The generic fibre is reduced, using the identity field extension in
   `def-pc-geometrically-irreducible`. Its dense open immersion is quasi-compact
   and quasi-separated by step 1. `lemma-nagata-reduced-dense-image-schematic`
   identifies its scheme-theoretic image with the generic fibre, and
   `lemma-nagata-scheme-image-ideal-qc` gives injectivity of the structure sheaf map.
   This is `def-trf-schematically-dense-open`.
5. `sbc-lem-smooth-geometrically-reduced` applied to step 2 gives geometrically
   reduced fibres of the smooth open. All arguments allow empty fibres. -/
theorem Scheme.Hom.smoothOpen_schematicGenericDensity {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [Flat f]
    [LocallyOfFinitePresentation f] [IrreducibleSpace Y]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    [GeometricallyReduced (f.fiberToSpecResidueField η)] :
    Dense (((f.fiberι η) ⁻¹ᵁ f.smoothLocus) : Set (f.fiber η)) ∧
    SchematicallyDenseOpen ((f.fiberι η) ⁻¹ᵁ f.smoothLocus) ∧
    (∀ y : Y, LocallyOfFiniteType (f.fiberToSpecResidueField y) ∧
      QuasiCompact (f.fiberToSpecResidueField y) ∧
      TopologicalSpace.NoetherianSpace (f.fiber y) ∧
      (∀ (T : Scheme.{u}) (j : T ⟶ f.fiber y),
        IsOpenImmersion j → QuasiCompact j ∧ QuasiSeparated j)) ∧
    (∀ y : Y, GeometricallyReduced
      (((f.fiberι y) ⁻¹ᵁ f.smoothLocus).ι ≫ f.fiberToSpecResidueField y)) := by
  sorry

end AlgebraicGeometry
