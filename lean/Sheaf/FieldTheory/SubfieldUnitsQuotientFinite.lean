/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Algebra.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Finite extensions from a finitely generated ambient unit quotient

Source: Stacks Project, Tag 04MK, `proposition-unique-base-field`, the quasi-compact
unit-quotient argument (blueprint: lem-sfb-subfield-units-quotient-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Subring

/-- Let `K` and `L` be field subrings of a nonzero commutative ring `A`. If the quotient
of `Aˣ` by the image of `Kˣ` is finitely generated, then `L` is finite-dimensional over
`K ⊓ L`, with scalars acting by the canonical inclusion.

Source: Stacks Project, Tag 04MK, `proposition-unique-base-field`, quasi-compact case
(blueprint: lem-sfb-subfield-units-quotient-finite).

Proof:
1. Put `F = K ⊓ L`. Inverses computed in `K` and `L` agree in `A` by uniqueness of
   inverses, so `F` is a field (`def-weil-field`). The nonzero elements of each field
   subring give ambient units.
2. The canonical homomorphism `Lˣ / Fˣ → Aˣ / Kˣ` is injective: an element of `Lˣ`
   mapping into `Kˣ` is exactly a unit of `F`.
3. A subgroup of a finitely generated abelian group is finitely generated: pull it
   back along a surjection from a finite power of `ℤ`, apply
   `Submodule.basisOfPid` (`lem-weil-subgroup-finite-free-abelian-group-free`), and
   push the finite basis forward. Thus `Lˣ / Fˣ` is finitely generated.
4. Choose representatives `α₁, …, αₛ` in `Lˣ`. Every nonzero element of `L` is a
   scalar in `Fˣ` times an integral-power monomial in the representatives. Evaluation
   on the representatives and their inverses gives a surjection from a polynomial
   ring in `2s` variables over `F` onto `L`; zero is the image of zero. Thus the
   inclusion is `RingHom.FiniteType` (`def-weil-pbc-finite-type-algebra`).
5. Apply `finite_of_finite_type_of_isJacobsonRing` (`lem-weil-pbc-zariski-lemma`)
   to the fields `F` and `L` and this finite-type algebra structure. This gives
   precisely the asserted finite module for the inclusion. -/
theorem finite_inf_of_fg_units_quotient {A : Type u} [CommRing A] [Nontrivial A]
    (K L : Subring A) (hK : IsField K) (hL : IsField L)
    [Group.FG (Aˣ ⧸ (Units.map K.subtype.toMonoidHom).range)] :
    @Module.Finite ↥(K ⊓ L) ↥L _ _
      (@Algebra.toModule _ _ _ _
        (Subring.inclusion (S := K ⊓ L) (T := L) inf_le_right).toAlgebra) := by
  sorry

end Subring
