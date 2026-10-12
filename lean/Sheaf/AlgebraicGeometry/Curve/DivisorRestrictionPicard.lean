/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard

/-! # Divisor restriction across a smooth curve compactification -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Restricting a divisor retains its coefficients and computes Picard pullback.
Source: blueprint, sec-curve-estimates/sk-prop-cd-affine/lem-sc-pic-affine, first paragraph,
restriction and boundary divisors
(blueprint: lem-sc-divisor-restriction-picard).

Proof: the open immersion is injective on points and identifies the local rings. A closed
point of C maps to a closed point of Z because it is rational over the algebraically closed
field and Z is separated over that field. Conversely a closed point of Z in the image has a
closed preimage by continuity and injectivity. Retain just the coefficients at these points;
this constructs a finitely supported divisor R on C. On a retained point the point-lift
comparison identifies the pullback of its point-ideal class with the class on C. On an omitted
point the boundary-triviality comparison gives the identity. Induct on the finite sum of
point divisors, using additivity and integer powers to obtain the Picard equality. If D is
zero, take R zero; if the boundary is empty every coefficient is retained. -/
theorem Scheme.Hom.exists_divisor_restriction_picard
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [hC : SmoothOfRelativeDimension 1 f] (D : c.Z.Divisor) :
    ∃ R : C.Divisor,
      (@Scheme.Divisor.toPic k _ C ⟨f⟩ hC R).toMul =
        Scheme.Pic.mapHom c.i (@Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm D).toMul ∧
      ∀ P : closedPoints c.Z, P.val ∈ Set.range c.i.base →
        ∃ Q : closedPoints C, c.i.base Q.val = P.val ∧ D P = R Q := by sorry

end AlgebraicGeometry
