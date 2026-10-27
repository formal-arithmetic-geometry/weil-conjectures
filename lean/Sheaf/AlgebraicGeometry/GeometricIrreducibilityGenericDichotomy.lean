/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

import Mathlib.AlgebraicGeometry.Properties
import Sheaf.TraceFormula.GeometricComponentCountGenericConstancy
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility

/-!
# Generic dichotomy for geometric irreducibility of fibres

Source: Stacks Project, More on Morphisms, Tags 055A and 055B, the second paragraph
of the proof of Tag 055B at the level `n = 1`
(blueprint: lem-trf-geometric-irreducibility-generic-dichotomy).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a nonempty relatively open subset of any irreducible closed subset of the target
of a finite type morphism, exactly one of universal geometric irreducibility of the fibres
and universal failure of geometric irreducibility holds. Empty fibres satisfy the latter.

Source: Stacks Project, More on Morphisms, Tags 055A and 055B, second paragraph of the
proof of Tag 055B at the level `n = 1`
(blueprint: lem-trf-geometric-irreducibility-generic-dichotomy).

Proof:
1. By scheme sobriety (lem-sc-scheme-sober), choose the generic point eta of Z. Apply
   geometricComponentCount_genericConstancy
   (lem-trf-geometric-component-count-generic-constancy) at eta. On a nonempty relative
   open V of Z, the fibres after separable closure have a constant component count n.
   The closures of def-pd-separable-closure are separably closed.
2. A space has exactly one irreducible component if and only if it is nonempty and
   irreducible: the components cover the space (lem-sc-irreducible-components-cover),
   and maximality (def-weil-irreducible-components) makes the full irreducible space
   its unique component. The empty space has no irreducible components.
3. For t in V, geometric irreducibility implies irreducibility after separable closure
   by def-pc-geometrically-irreducible. Conversely, apply
   isIrreducible_preimage_of_isSepClosed_extension
   (lem-sbc-subset-geometric-irreducibility) to the full subset of the fibre. It gives
   irreducibility and nonemptiness after every field extension, hence geometric
   irreducibility. Thus geometric irreducibility of the fibre is equivalent to n = 1.
4. Split into n = 1 and n different from 1. These give the two alternatives, respectively.
   They cannot both hold, since V is nonempty. Empty fibres have component count zero.
No flatness or Noetherian hypothesis is used.
-/
theorem geometricallyIrreducible_genericDichotomy
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set Y) (hZclosed : IsClosed Z) (hZirreducible : IsIrreducible Z) :
    ∃ V : Set Z, IsOpen V ∧ V.Nonempty ∧
      Xor (∀ t : Z, t ∈ V → GeometricallyIrreducible (f.fiberToSpecResidueField t.val))
        (∀ t : Z, t ∈ V → ¬ GeometricallyIrreducible (f.fiberToSpecResidueField t.val)) := by
  sorry

end AlgebraicGeometry
