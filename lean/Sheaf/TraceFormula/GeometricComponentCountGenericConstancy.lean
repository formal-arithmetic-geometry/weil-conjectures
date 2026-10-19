/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.Irreducible
public import Mathlib.SetTheory.Cardinal.Finite

import Sheaf.TraceFormula.GeometricFibreComponentCountBaseChange
import Sheaf.TraceFormula.GenericFibreComponentLowerBound
import Sheaf.AlgebraicGeometry.GenericComponentsSplit
import Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread
import Sheaf.AlgebraicGeometry.EtaleGenericResidueFieldModel
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Generic constancy of geometric fibre component counts

Source: literature/stacks-project/more-morphisms.tex, Tag 055A
(blueprint: lem-trf-geometric-component-count-generic-constancy).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- For a finite-type morphism, the number of irreducible components of the geometric
fibres is constant on a nonempty relatively open subset of the closure of every point.

Source: literature/stacks-project/more-morphisms.tex, Tag 055A
(blueprint: lem-trf-geometric-component-count-generic-constancy).

Proof: Reduce to the reduced closure of the chosen point and use finite separable
component splitting at the generic fibre. Spread the resulting geometric component
cover to obtain an upper bound on a neighbourhood. Spread the finite etale residue-field
model and apply the ordinary generic-fibre component lower-bound theorem. Compare
ordinary and geometric component counts after a separable closure, then descend the
equalities along the open etale map. Base-change invariance gives independence of all
separable-closure choices. The argument allows the empty fibre and the value zero.
-/
theorem geometricComponentCount_genericConstancy
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ n : ℕ,
      ∀ t : Y, t ∈ V ∩ closure {y} →
        ∀ (K : Type u) [Field K] [Algebra (Y.residueField t) K]
          [IsSepClosure (Y.residueField t) K],
          ENat.card (irreducibleComponents
            ↥(pullback f
              (Spec.map (CommRingCat.ofHom
                (algebraMap (Y.residueField t) K)) ≫
                Y.fromSpecResidueField t))) = n := by
  sorry

end AlgebraicGeometry
