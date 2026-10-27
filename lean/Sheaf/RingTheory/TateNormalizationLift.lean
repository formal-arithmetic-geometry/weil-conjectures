/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Noether normalization lifted to a Tate presentation

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2,
Corollary 10, printed p. 14 (blueprint: lem-trf-tate-normalization-lift).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- A proper quotient of a Tate algebra has a finite injective normalization that
lifts to the original Tate algebra. Scalar compatibility with `constants` expresses
that the lifted ring homomorphism is a `K`-algebra homomorphism. In zero variables,
all series are constants, so the source is canonically `K`.

Source: Bosch, Section 1.2, Corollary 10, printed p. 14
(blueprint: lem-trf-tate-normalization-lift).

Proof (the node's expanded assembly of Bosch's induction).
1. Induct on the number of variables. For the zero ideal use the identity and `d = r`.
For zero variables the ring is `K`, whose only proper ideal is zero.
2. Otherwise choose a nonzero element of the ideal. Apply
lem-per-tate-triangular-distinguished-coordinate to obtain a coordinate automorphism
and a unit multiple of the transformed element that is normalized distinguished.
Apply lem-trf-tate-weierstrass-norm-division: the quotient by the transformed ideal
is generated over the ring in one fewer variable by the powers below its distinguished
degree. Degree zero would make the ideal improper, so this degree is positive.
3. Include the ring in one fewer variable by inserting a zero last exponent. Contract
the transformed ideal to the kernel of its map to the quotient. This kernel is proper,
and its quotient injects into the original quotient. Apply induction to that kernel
to obtain a lifted finite injective normalization in at most `r - 1` variables.
4. Multiply the finitely many inductive generators by the finitely many powers from
division to obtain generators over the smaller Tate algebra. Compose the inductive
lift with the inclusion and the inverse coordinate automorphism. The isomorphism
from the transformed quotient to the original quotient transports these generators
and identifies its scalar action with the quotient composite of this precise lift.
It also proves that composite injective; the lift is itself a composite of injections.
Finally `d ≤ r - 1 ≤ r`, and the zero-variable source consists exactly of constants.
-/
theorem tate_normalization_lift
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (hK : ∃ a : K, a ≠ 0 ∧ ‖a‖ ≠ 1) (r : ℕ)
    (I : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := K)
      (fun _ : Fin r ↦ (1 : ℝ)))) (hI : I ≠ ⊤) :
    ∃ d : ℕ, d ≤ r ∧
      ∃ ι : ↥(MvPowerSeries.IsRestricted.subring (R := K)
          (fun _ : Fin d ↦ (1 : ℝ))) →+*
          ↥(MvPowerSeries.IsRestricted.subring (R := K)
            (fun _ : Fin r ↦ (1 : ℝ))),
        Function.Injective ι ∧
        ι.comp (constants K d) = constants K r ∧
        Function.Injective ((Ideal.Quotient.mk I).comp ι) ∧
        ((Ideal.Quotient.mk I).comp ι).Finite := by
  sorry

end RestrictedSeries
