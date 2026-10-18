module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat

/-! # Smoothness at generic points of geometrically reduced fibres

Source: literature/stacks-project/varieties.tex, Tag 056V, together with
literature/stacks-project/morphisms.tex, Tag 01V9
(blueprint: lem-trf-generic-fibre-points-smooth).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Let `p : Z ⟶ S` be a flat, locally finitely presented morphism of Noetherian
schemes whose geometric fibres are reduced.  At the generic point of every
irreducible component of every fibre, `p` is smooth on a neighbourhood.

Source: Stacks Project, Varieties, Tag 056V, together with Morphisms, Tag 01V9.
(blueprint: lem-trf-generic-fibre-points-smooth)

Proof: For a fixed fibre, affine finite-presentation charts and the
finite-purely-inseparable criterion identify the assumed geometric reducedness
with reducedness after every field extension.  Tag 056V gives a dense smooth
locus in that fibre.  On a Noetherian affine neighbourhood of a component
generic point, only finitely many irreducible components occur, so the dense
smooth locus contains the generic point.  The pointwise flat-fibre criterion
of Tag 01V9 then upgrades fibrewise smoothness to smoothness of `p` on an open
neighbourhood of the point.
-/
theorem generic_fibre_points_smooth
    {Z S : Scheme.{u}} [IsNoetherian Z] [IsNoetherian S]
    (p : Z ⟶ S) [Flat p] [LocallyOfFinitePresentation p]
    (hred : ∀ s : S, GeometricallyReduced (p.fiberToSpecResidueField s))
    (s : S) (C : Set (p.fiber s))
    (hC : C ∈ irreducibleComponents (p.fiber s))
    (z : p.fiber s) (hz : IsGenericPoint z C) :
    ∃ W : Z.Opens, p.fiberι s z ∈ W ∧ Smooth (W.ι ≫ p) := by
  sorry

end AlgebraicGeometry
