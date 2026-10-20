/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Connected.Basic

import Mathlib.Topology.Constructible
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible
import Sheaf.AlgebraicGeometry.FlatReducedSectionComponentGeneralization

/-!
# Openness of the section component in a flat family with geometrically reduced fibres

Source: Stacks Project, Tag 055R, `lemma-connected-along-section-open`, using
Tags 055P and 055Q (blueprint: lem-trf-flat-reduced-section-component-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a flat morphism of finite presentation whose fibres are geometrically reduced,
the union of the fibre connected components containing the section is open.
The scheme-theoretic fibre is identified with its underlying subspace by `g.fiberHomeo`.

Source: Stacks Project, Tag 055R, `lemma-connected-along-section-open`.

Proof:
1. Tag 055P (`lem-sbc-section-component-locally-constructible`) makes the section-component
   locus locally constructible, using local finite presentation, quasi-compactness and
   quasi-separatedness.
2. Tag 055Q (`lem-trf-flat-reduced-section-component-generalization`) makes this locus
   stable under generalization, using flatness and geometrically reduced fibres.
3. Around a point of the locus choose an affine open by `lem-weil-pbc-affine-opens-basis`.
   Restrict local constructibility and generalization stability to this open. It is qcqs
   by `lem-weil-pbc-affine-scheme-qcqs`, so `lem-trf-locally-constructible-qcqs-global`
   makes the restricted locus constructible. The criterion
   `lem-trf-spectrum-constructible-generalization-open` then makes it open on this chart.
4. The resulting open neighbourhoods are open in the source, contained in the locus,
   and cover it. Their union is the locus, which is therefore open.

(blueprint: lem-trf-flat-reduced-section-component-open) -/
theorem isOpen_section_component_of_flat_of_geometricallyReduced_fibers
    {P T : Scheme.{u}} (g : P ⟶ T) [Flat g] [LocallyOfFinitePresentation g]
    [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    (hred : ∀ t : T, GeometricallyReduced (g.fiberToSpecResidueField t)) :
    IsOpen {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  sorry

end AlgebraicGeometry
