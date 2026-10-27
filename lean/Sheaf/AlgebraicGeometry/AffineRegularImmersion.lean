/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular immersions over arbitrary schemes

Source: Stacks Project, Divisors, Tags 063G and 063J
(blueprint: def-sfb-affine-regular-immersion).

The affine presentations are required near source points. Their lengths may vary, and
the immersion need not be closed in its whole target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An immersion is regular if each source point has an open neighbourhood identified
over the target with the spectrum of a quotient by a finite regular sequence in an
affine open of the target. The sequence may be empty. No Noetherian hypothesis or
constant codimension is imposed.
Source: Stacks Project, Divisors, Tags 063G and 063J
(blueprint: def-sfb-affine-regular-immersion). -/
def IsAffineRegularImmersion {T W : Scheme.{u}} (a : T ⟶ W) : Prop :=
  IsImmersion a ∧ ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
    ∃ (A : CommRingCat.{u}) (r : List A), RingTheory.Sequence.IsRegular A r ∧
      ∃ (e : Spec A ⟶ W), IsOpenImmersion e ∧
        ∃ q : V.toScheme ≅ Spec (CommRingCat.of (A ⧸ Ideal.ofList r)),
          V.ι ≫ a = q.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ e

end AlgebraicGeometry
