/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H2
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Ring.ULift

/-!
# Representations and modules over a lifted group ring

Source: Stacks Project, Injectives, Section G-modules, immediately before Tag 04JF.
(blueprint: lem-exc-rg-representation-lifted-group-algebra-equivalence).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace Rep

/-- (blueprint: lem-exc-rg-representation-lifted-group-algebra-equivalence)
Source: Stacks Project, Injectives, Section G-modules, immediately before Tag 04JF:
R-linear G-actions are the same as modules over the group ring.

Proof: replace R by its isomorphic lifted ring using the ring isomorphism
`ULift.ringEquiv`. On a representation V, let a group-ring element act by the finite
sum of its coefficients acting on the corresponding translates of V. The representation
law, R-linearity of the action, and the convolution multiplication prove the module
laws, including for noncommutative R: the group action commutes with all R-scalars.
An intertwining map commutes with this finite sum and is therefore group-ring linear.
Conversely restrict a group-ring module along the inclusion of R and let g act by the
singleton basis element at g with coefficient 1. Multiplication of these basis elements
proves the action law; they commute with constant coefficients, proving R-linearity.
A group-ring linear map is then an intertwining map. Restriction followed by extension
recovers the original action, and extension followed by restriction recovers the original
module action by expansion in singleton basis elements. Identity maps on the underlying
additive groups give the natural unit and counit isomorphisms and their triangle laws.
No carrier changes universe: all carriers lie in max u v w, and the coefficient lift
merely allows the group-ring embedding theorem to run at this same carrier universe. -/
theorem representation_liftedGroupAlgebra_equivalence
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{max u v w} R G ≌
      ModuleCat.{max u v w} (MonoidAlgebra (ULift.{w} R) G)) := by
  sorry

end Rep
