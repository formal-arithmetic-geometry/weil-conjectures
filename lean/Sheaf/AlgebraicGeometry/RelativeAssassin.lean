/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes

/-! # Associated points of a module and the relative assassin

Source: Stacks Project, Divisors, Tags 02OJ and 05AT
(blueprint: def-trf-relative-assassin).

## Main definitions

* `Scheme.Modules.associatedPoints`: association of the maximal ideal of the stalk ring.
* `Scheme.Modules.relativeAssassin`: fibrewise associated points, viewed on the total space.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Associated points of a sheaf of modules: the maximal ideal of the local ring is
an element-annihilator associated prime of its stalk module.
Source: Stacks Project, Divisors, Tag 02OJ (blueprint: def-trf-relative-assassin). -/
def associatedPoints {X : Scheme.{u}} (F : X.Modules) : Set X :=
  {x | IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
    RingTheory.annihilatorAssociatedPrimes (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)}

/-- The relative assassin consists of the associated points of the tensor pullback to
one's own scheme-theoretic fibre. This is the union in Stacks 05AT, written using
`f.asFiber` to regard a point as a point of its fibre.
Source: Stacks Project, Divisors, Tag 05AT (blueprint: def-trf-relative-assassin). -/
def relativeAssassin {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Set X :=
  {x | f.asFiber x ∈ associatedPoints ((tensorPullback (f.fiberι (f x))).obj F)}

end AlgebraicGeometry.Scheme.Modules
