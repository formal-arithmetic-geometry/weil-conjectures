/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.Ample

/-! # Transition functions between section trivializations

Source: Stacks Project, Modules, Lemma 01CY; Properties, proofs of 01PV and 01PY.
(blueprint: lem-weil-pbc-nonvanishing-transition-functions)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Two nonvanishing section opens of the same invertible module intersect in a basic
open; their transition coefficients multiply to one on the intersection.

Source: Stacks Project, Modules, Lemma 01CY; Properties, proofs of Lemmas 01PV and 01PY.
(blueprint: lem-weil-pbc-nonvanishing-transition-functions)

Proof: s trivializes M on U and t trivializes M on V by Lemma 01CY. Thus there are
unique coefficients f in O(U) and g in O(V) with t|U = f*s|U and s|V = g*t|V.
For a point x in U, the value of s is a nonzero basis vector of the one-dimensional
residue fibre. The value of t is f(x) times this basis, so it is nonzero exactly when
f(x) is nonzero. Outside U, neither U intersect V nor the basic open of f has points.
Consequently U intersect V equals the basic open of f. Restricting both coefficient
equations to U intersect V and substituting gives t = f*g*t. Since t trivializes M
there, uniqueness of its coefficient gives f*g = 1. This also covers an empty
intersection, whose section ring is the zero ring.
-/
theorem exists_nonvanishing_transition_functions {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (s t : M.val.presheaf.obj (Opposite.op ⊤))
    (U V : X.Opens) (hU : (U : Set X) = nonvanishingLocus M s)
    (hV : (V : Set X) = nonvanishingLocus M t) :
    ∃ (f : Γ(X, U)) (g : Γ(X, V)), U ⊓ V = X.basicOpen f ∧
      (X.presheaf.map (homOfLE inf_le_left).op) f *
        (X.presheaf.map (homOfLE inf_le_right).op) g = 1 := by sorry

end AlgebraicGeometry.Scheme.Modules
