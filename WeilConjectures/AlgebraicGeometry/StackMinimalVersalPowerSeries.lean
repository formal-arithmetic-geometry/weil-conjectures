/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.RingTheory.MvPowerSeries.Basic
import WeilConjectures.AlgebraicGeometry.ArtinLocalTestAlgebra

/-! # Comparison of versal rings by formal variables

Source: Stacks Project, formal-defos.tex, Tag 06T5 (lemma-minimal-versal),
and stacks-geometry.tex, Tag 0DQX (lemma-versal-ring)
(blueprint: lem-sfb-stack-minimal-versal-power-series).

The specified residue map of a power series algebra is its constant coefficient
followed by the specified residue map of its coefficient algebra. An algebra
equivalence between local rings preserves their maximal ideals and all their
powers, so it is automatically an isomorphism for the maximal-ideal adic structures.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AlgebraicGeometry.ArtinDeformation

/-- Two marked versal rings differ by finitely many formal variables.
Source: Stacks, Tags 06T5 and 0DQX
(blueprint: lem-sfb-stack-minimal-versal-power-series).

Proof: First localize R at the kernel of R → l. The localization comparison of
lem-sfb-artin-local-test-algebra makes l module-finite over that local base and
identifies both the Artinian test and complete marked algebra categories.
Versality implies (S1): use lem-sfb-versal-formal-object-quasi-initial to map a
versal object to the first object in a fibre-product datum; lift along the
surjective second leg using the specified identification. Evaluate on the
resulting map into the literal fibre-product test algebra to realize that datum.
Apply lem-sfb-versal-minimal-subring-descent to each versal object. Then
lem-sfb-versal-descended-base-power-series gives marked presentations
C ≃ B_C[[x₁,…,x_a]] and D ≃ B_D[[y₁,…,y_b]]. Quasi-initiality gives maps between
the two minimal objects in both directions. Incoming-map minimality makes the
underlying ring maps surjective. A surjective endomorphism of a Noetherian ring
is injective: its ascending kernel chain stabilizes, and lifting a kernel
element through a sufficiently high power forces it to vanish. Thus the minimal
bases are isomorphic by a local residue-preserving map; identify them with B.
Compare a and b. If a ≤ b, regroup the coefficients indexed by the first a and
the remaining b-a variables to identify D with C[[t₁,…,t_{b-a}]]. Otherwise
interchange C and D. Regrouping preserves the finite convolution sums defining
multiplication and the constant coefficient, hence the residue marking. Equal
numbers of variables give r = 0. Restrict scalars back to R.
-/
theorem stack_minimal_versal_power_series
    {R l : Type u} [CommRing R] [IsNoetherianRing R] [Field l] [Algebra R l]
    [Algebra.FiniteType R l] (F : CofibredGroupoids.{u, v, w} R l)
    (hF : IsPredeformation F) (C D : CompleteLocalAlgebra R l)
    (ξ : FormalObject F C) (η : FormalObject F D)
    (hξ : IsVersal ξ) (hη : IsVersal η) :
    ∃ r : ℕ,
      (∃ e : C.ring ≃ₐ[R] MvPowerSeries (Fin r) D.ring,
        ∀ c : C.ring,
          D.residueEquiv (IsLocalRing.residue D.ring (MvPowerSeries.constantCoeff (e c))) =
            C.residueEquiv (IsLocalRing.residue C.ring c)) ∨
      (∃ e : D.ring ≃ₐ[R] MvPowerSeries (Fin r) C.ring,
        ∀ d : D.ring,
          C.residueEquiv (IsLocalRing.residue C.ring (MvPowerSeries.constantCoeff (e d))) =
            D.residueEquiv (IsLocalRing.residue D.ring d)) := sorry

end AlgebraicGeometry.ArtinDeformation
