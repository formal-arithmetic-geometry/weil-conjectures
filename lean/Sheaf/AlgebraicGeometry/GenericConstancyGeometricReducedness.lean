/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.GenericFibreGeometricallyReducedOpen
import Sheaf.AlgebraicGeometry.GenericFibreNotGeometricallyReducedOpen

/-!
# Generic constancy of geometric reducedness of fibres

Source: Stacks Project, More on Morphisms, Tags 0577 and 0578
(blueprint: lem-trf-generic-constancy-geometric-reducedness).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a quasi-compact locally finitely presented morphism to an irreducible scheme,
geometric reducedness of the fibres agrees with that of the generic fibre on some
nonempty open subset. Fibres carry their canonical residue-field structure maps.

Source: Stacks Project, More on Morphisms, Tags 0577 and 0578.
(blueprint: lem-trf-generic-constancy-geometric-reducedness)

Proof:
1. Local finite presentation implies local finite type, since finitely presented
   algebras are finitely generated; the affine-local condition is unchanged on
   principal-open refinements. Together with quasi-compactness this makes `f` finite
   type (def-sbc-locally-finite-presentation, def-weil-finite-type-morphism).
2. Split on geometric reducedness of the generic fibre. In the positive case,
   lem-trf-generic-fibre-geometrically-reduced-open (Tag 0578) gives a nonempty
   open on which every fibre is geometrically reduced. In the negative case,
   lem-trf-generic-fibre-not-geometrically-reduced-open (Tag 0577) gives a nonempty
   open on which no fibre is geometrically reduced. Each case gives the equivalence.
   This includes empty fibres and assumes neither flatness nor reducedness or
   Noetherianity of the base. -/
theorem exists_nonempty_open_geometricallyReduced_fiber_iff_generic
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFinitePresentation f]
    [IrreducibleSpace Y] (η : Y) (hη : IsGenericPoint η Set.univ) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ y : Y, y ∈ V →
        (GeometricallyReduced (f.fiberToSpecResidueField y) ↔
          GeometricallyReduced (f.fiberToSpecResidueField η)) := by
  sorry

end AlgebraicGeometry
