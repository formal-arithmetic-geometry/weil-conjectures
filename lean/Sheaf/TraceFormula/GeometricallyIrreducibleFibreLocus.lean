/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion
import WeilConjectures.AlgebraicGeometry.RadicialPreparationFibreComparison
import Sheaf.AlgebraicGeometry.SubsetGeometricIrreducibility
import Sheaf.TraceFormula.GeometricComponentCountGenericConstancy
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Constructibility of the geometrically irreducible fibre locus

Source: literature/stacks-project/more-morphisms.tex, Tag 055B
(blueprint: lem-trf-geometrically-irreducible-fibre-locus).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry

/-- For a finitely presented map of commutative rings, the locus on the base whose
geometric fibres are irreducible is constructible.

Source: literature/stacks-project/more-morphisms.tex, Tag 055B (lemma-nr-geom-
irreducible-components-constructible), affine ring form.

Proof: Choose a finite presentation and descend it to a finite type algebra over a
finite type subalgebra of `ℤ`.  The geometric irreducibility locus over that Noetherian
base is locally constant on irreducible closed subsets by generic constancy of the
number of geometric components.  Identify the original family as a base change and
pull back the constructible locus along the induced map of spectra.  The proof uses
`def-weil-pbc-finitely-presented-algebra`, `lem-weil-pbc-algebra-tensor-pushout-
universal-property`, `def-weil-finite-type-morphism`,
`lem-weil-pbc-finite-type-over-noetherian`, `lem-sc-scheme-sober`,
`lem-trf-geometric-component-count-generic-constancy`,
`lem-sc-irreducible-components-cover`, `def-weil-irreducible-components`,
`def-pc-geometrically-irreducible`, `lem-sbc-subset-geometric-irreducibility`,
`def-pd-separable-closure`, `lem-trf-noetherian-constructible-subset-criterion`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-sbc-radicial-preparation-fibre-comparison`,
`def-weil-universal-homeomorphism`, and
`lem-pur-scheme-constructible-preimage`.
(blueprint: lem-trf-geometrically-irreducible-fibre-locus).
-/
theorem geometricallyIrreducible_fibre_locus_constructible
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] :
    Topology.IsConstructible
      {p : PrimeSpectrum A |
        GeometricallyIrreducible
          (Spec.map (CommRingCat.ofHom
            (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))))} := by
  sorry

end
