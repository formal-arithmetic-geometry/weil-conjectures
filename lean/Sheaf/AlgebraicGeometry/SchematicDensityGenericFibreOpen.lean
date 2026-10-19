import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.AffineSchematicDensityCriterion
import WeilConjectures.RingTheory.GenericFlatness

/-!
# Schematic density in fibres spreads from the generic fibre

Source: literature/stacks-project/more-morphisms.tex, Tag 0573,
  lemma-scheme-theoretically-dense-generic-fibre; schematic-density meaning: morphisms.tex Tag 01RE,
  lemma-characterize-scheme-theoretically-dense.
(blueprint: lem-trf-schematic-density-generic-fibre-open)
-/

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- For a finite type morphism over an irreducible scheme, schematic density of an open in the
    generic fibre spreads to every fibre over a nonempty open of the base.

    Proof plan from Stacks Tag 0573: reduce the base to an integral affine open and choose a
    finite affine cover of the finite-type source. On each chart, quasi-compactness of the
    generic fibre gives finitely many principal opens inside `U`; the affine density criterion
    gives an injective multiplication map and its cokernel. Apply algebra generic flatness to
    the square-zero algebra formed from the chart algebra and this cokernel, obtaining a
    localization where both summands are flat. Torsion-freeness and localization by fractions
    preserve exactness, so tensoring with each residue field preserves injectivity. The affine
    criterion gives density on each fibre chart, and a finite intersection of the base opens
    glues the result. The empty-source case has any nonempty base open as the witness.

    (blueprint: lem-trf-schematic-density-generic-fibre-open) -/
theorem schematicDensityGenericFibreOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : IsIrreducible (Set.univ : Set Y)) (η : Y)
    (hη : IsGenericPoint η (Set.univ : Set Y)) (U : X.Opens)
    (hηdense : ∀ W : (f.fiber η).Opens,
      Function.Injective ((pullback.snd U.ι (f.fiberι η)).app W)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ (y : Y), y ∈ (V : Set Y) →
        ∀ W : (f.fiber y).Opens,
          Function.Injective ((pullback.snd U.ι (f.fiberι y)).app W) := by
  sorry

end AlgebraicGeometry
