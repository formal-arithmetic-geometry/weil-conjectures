/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Core local acyclicity for smooth morphisms.

Source: Stacks Project, Tag 0GJQ, strict-local calculation in the proof of
proposition-smooth-locally-acyclic (blueprint: lem-weil-pbc-smooth-local-acyclicity-core).

The proof follows the strict-local reduction: after restricting to an affine open on which the
coefficient order is invertible, smooth base change identifies the exchange map with pullback on
strict-local cohomology; the geometric-fibre test reduces this to cohomology of a separably closed
field, where constant coefficients are acyclic. The canonical germ and section maps are tracked
through inverse-image composition, yielding the defining alpha isomorphism and positive-degree
vanishing for every geometric point and every allowed coefficient order.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The strict-local calculation for smooth local acyclicity.

Proof: restrict to an affine open where the coefficient order is invertible. Smooth base change,
strict-local exchange, and the geometric-fibre test identify the defining alpha with pullback from
a separably closed field. Constant cohomology on that field is the coefficient group in degree zero
and vanishes positively; germ compatibility identifies this map with the canonical alpha.
Source: Stacks Project, Tag 0GJQ, proposition-smooth-locally-acyclic.
(blueprint: lem-weil-pbc-smooth-local-acyclicity-core)
-/
theorem smooth_localAcyclicity_core {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    IsLocallyAcyclic f := by
  sorry

end AlgebraicGeometry.Etale
