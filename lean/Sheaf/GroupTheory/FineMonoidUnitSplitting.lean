/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Splitting a fine monoid over its sharpening

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.11 and 3.1.26, printed pp. 100, 102;
agent algebraic refinement with the explicit torsion-free sharp-group hypothesis
(blueprint: lem-trf-fine-monoid-unit-splitting).
-/

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.FineFan

/-- A fine monoid whose completion and sharp completion are torsion-free splits over its
sharpening, with a finite free unit factor. We use multiplicative notation, as in `IsFine`:
`Associates P` is the quotient by units, and `Multiplicative (Fin s → ℤ)` represents `ℤ^s`.
The second formulation specifies the isomorphism by the formula `(b, u) ↦ j b * u`.

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.11 and 3.1.26, printed pp. 100, 102;
agent algebraic refinement, not an assertion for every fine torsion-free monoid
(blueprint: lem-trf-fine-monoid-unit-splitting).

Proof:
1. Write `G = P^gp` and identify `P` with its image using `IsFine`. The units form a subgroup
   `U` of `G`. The map `B = P/U → G/U` is injective: equality of cosets is exactly differing
   by a unit. Thus `B` is integral. The induced surjection `G → H = B^gp` has kernel `U`:
   a difference maps to zero precisely when its two numerators have the same unit class.
   These are direct checks with the group completion and unit relation of
   def-trf-fine-fan-blowup and def-trf-fs-log-blowup.
2. A finite monoid generating list for `P` maps to generators of `B`, hence to group
   generators of `H`. The assumed torsion-freeness of `H` and
   lem-trf-fg-torsionfree-group-free (`Module.basisOfFiniteTypeTorsionFree'` over `ℤ`)
   give a finite basis of `H`.
3. Lift each basis vector to `G`. Integer linear combinations of these lifts define a
   group section `t : H → G`. The basis-coordinate formula proves that its composite
   with `G → H` is the identity, including when the basis is empty.
4. For `b ∈ B`, lift it to `p ∈ P`. Then `t(b) - p` lies in the kernel `U`. Since every
   unit and its inverse belong to `P`, `t(b)` belongs to `P`. Restricting `t` therefore
   gives a monoid section `j : B → P`, independent of the auxiliary lift `p`.
5. The maps `(b,u) ↦ j(b)+u` and `p ↦ (q(p),p-j(q(p)))` are inverse monoid maps.
   The kernel calculation puts the second coordinate in `U`. Direct substitution
   verifies both inverse equations and that `q` is the first projection.
6. In a finite generating list of `P`, every generator occurring in a unit is a unit:
   if `u=a+v` is a unit, then `a+(v-u)=0`, with `v-u ∈ P`. The unit generators thus
   generate `U`. It is torsion-free as a subgroup of `G`, so
   lem-trf-fg-torsionfree-group-free gives `U ≃ ℤ^s` for some `s : ℕ`.
   Composing this coordinate isomorphism with the product decomposition gives the
   first formulation. No saturation assumption is used. -/
theorem fine_monoid_unit_splitting
    (P : Type u) [CommMonoid P] (hP : IsFine P)
    [IsMulTorsionFree (Algebra.GrothendieckGroup P)]
    [IsMulTorsionFree (Algebra.GrothendieckGroup (Associates P))] :
    ∃ s : ℕ,
      (∃ e : P ≃* (Associates P × Multiplicative (Fin s → ℤ)),
        ∀ p : P, (e p).1 = Associates.mk p) ∧
      ∃ j : Associates P →* P,
        (∀ b : Associates P, Associates.mk (j b) = b) ∧
        (∃ f : (Associates P × Pˣ) ≃* P,
          ∀ (b : Associates P) (u : Pˣ), f (b, u) = j b * (u : P)) ∧
        Nonempty (Pˣ ≃* Multiplicative (Fin s → ℤ)) := by
  sorry

end AlgebraicGeometry.FineFan
