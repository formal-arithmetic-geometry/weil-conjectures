/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.RingTheory.HeightOneFractionOrder

/-! # Locally finite codimension-one cycles and their local equations

Source: EGA IV4, Sections 21.6 and 21.13.15; Stacks Project, Divisors, Tag 0BE2
(blueprint: def-sfb-locally-finite-principal-cycle).

A locally finite cycle is Mathlib's `AlgebraicCycle X ℤ` (Stacks 02QR): a coefficient at
every point, with locally finite support. A point `z` stands for the closure of `{z}`.
An open set meets this closure exactly when it contains `z`, so locally finite support is
the same as local finiteness of the family of closures of the nonzero terms. Codimension one
is the condition that nonzero coefficients sit at points with one-dimensional local ring,
stated as a hypothesis where it is used. This module adds only principality at a point.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- A local equation for a cycle is a nonzero fraction with its prescribed orders at
all height-one primes of the stalk. The corresponding generization of `x` is the image
under Mathlib's canonical `fromSpecStalk`, not an independently chosen point map.
`hd` and `hn` express normality of this stalk, and are passed to the existing fraction order.
Source: EGA IV4, Section 21.6 and Corollary 21.13.15; Stacks Tags 00PD and 02RJ
(blueprint: def-sfb-locally-finite-principal-cycle). -/
def IsPrincipalAt {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : AlgebraicCycle X ℤ) (x : X)
    (hd : IsDomain (X.presheaf.stalk x)) (hn : IsIntegrallyClosed (X.presheaf.stalk x)) :
    Prop :=
  ∃ a : (FractionRing (X.presheaf.stalk x))ˣ,
    ∀ q : Ring.WeilHeightOnePrime (X.presheaf.stalk x),
      @Ring.weilFractionOrder (X.presheaf.stalk x) _ hd inferInstance hn q a =
        D ((X.fromSpecStalk x) q.val)

end AlgebraicGeometry.AlgebraicCycle
