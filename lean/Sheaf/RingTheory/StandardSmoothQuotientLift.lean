/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-! # Lifting a standard smooth algebra across a quotient of its base

Source: Stacks Project, Tag 07CK, the Jacobian presentation construction of `B`.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A standard smooth algebra over `R/I` is the reduction of a standard smooth
algebra over `R`. This only lifts the presentation, not a map into another algebra.

Source: Stacks Project, Smoothing Ring Maps, Tag 07CK (lemma-lift-once), the construction
of `B` (blueprint: lem-weil-pbc-standard-smooth-quotient-lift).

Proof: Choose a finite submersive presentation of `C` over `R/I`, with equations
`fbar` and an invertible Jacobian minor `Dbar`. Lift the coefficients of its finitely
many equations to `R`, giving equations `f`, and let `D` be the corresponding Jacobian
minor. Form the finite polynomial quotient `B = R[x,z]/(f,z*D-1)`. Choose the old
minor variables together with `z`. Since the equations `f` do not involve `z`, this
Jacobian matrix is block triangular, with the old matrix and `D` on its diagonal.
Its determinant is `D^2`, a unit in `B` since `z*D=1`. Thus this quotient has a
submersive presentation and is standard smooth. Reduction of polynomial coefficients
commutes with partial derivatives and determinants. Reducing `B` modulo `I` gives
`(R/I)[x,z]/(fbar,z*Dbar-1)`. Map it to `C` by the presentation generators and send
`z` to the inverse of `Dbar`. The inverse sends the presentation generators of `C`
to the classes of `x`. The composites fix these generators and also `z`, since
inverses are unique. Both maps commute with the `R/I`-algebra structure. The quotient
has universe at most `u`; lift its carrier to `max u v` and transport the structures
and equivalence. Empty equation lists use determinant `1` and eliminate `z`; the
zero algebra is covered by the same presentation argument. No property of `I` other
than being an ideal is used. -/
theorem exists_standardSmooth_quotient_lift
    (R : Type u) [CommRing R] (I : Ideal R)
    (C : Type v) [CommRing C] [Algebra (R ⧸ I) C] [IsStandardSmooth (R ⧸ I) C] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      IsStandardSmooth R B ∧
        Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R ⧸ I] C) := by sorry

end Algebra
