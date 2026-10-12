/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
import Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# Comparison of the two divisor-module constructions

Source: blueprint lem-sc-divisor-class-curve, homomorphism step, and
lem-pc-divisor-line-bundle-agrees-sc; Stacks Project, Divisors, Tag 02SL.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The point-ideal construction of the Picard class of an arbitrary divisor has the
valuation-bounded divisor module as a representative.
Source: blueprint lem-sc-divisor-class-curve, Proof (tensor-product compatibility), and
lem-pc-divisor-line-bundle-agrees-sc, Proof; Stacks Project, Divisors, Tag 02SL
(blueprint: lem-sc-divisor-toPic-representative).

Proof: Write D = E₁ - E₂ using its positive and negative parts. For an effective divisor E,
the ideal sheaf is the product of the point ideals to their multiplicities. Its dual is
O(E), by lem-pc-divisor-line-bundle-agrees-sc. In particular the class of each point ideal
dual is the class of its valuation-bounded module. Multiplication of rational sections
induces O(A) tensor O(B) -> O(A+B). At a closed point P, choose a common uniformizer t;
lem-sc-divisor-module-local identifies the two source factors with t^(-A(P)) O and
t^(-B(P)) O and the target with t^(-A(P)-B(P)) O. Multiplication is an isomorphism under
these identifications. These neighbourhoods cover the curve (the generic point lies in
every nonempty open), so multiplication is an isomorphism globally. The zero divisor
module is the structure module. Taking B = -A gives O(-A) as the inverse Picard class.
Consequently O(D) has class [I(E₁)^dual] [I(E₂)], exactly Divisor.toPic k C D by
Divisor.toMul_toPic_mapRange_sub and Divisor.mapRange_toNat_sub. Equal Picard classes
have isomorphic representatives, giving the asserted isomorphism. This also handles
D = 0, negative divisors, and curves that are not proper; no properness is used. -/
theorem Divisor.nonempty_toPic_iso_module
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsConnectedCurve (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] (D : C.Divisor) :
    Nonempty ((fromSkeleton C.Modules).obj (Divisor.toPic k C D).toMul.val ≅
      D.moduleOfSmoothConnectedCurve k C (C ↘ Spec (.of k))) := by sorry

end AlgebraicGeometry.Scheme
