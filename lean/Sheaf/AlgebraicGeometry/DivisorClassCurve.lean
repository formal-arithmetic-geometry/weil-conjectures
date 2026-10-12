/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModuleLocal
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import Sheaf.AlgebraicGeometry.DivisorModule
import Sheaf.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# Divisor classes and the Picard group of a smooth connected curve

Source: blueprint, sec-curve-estimates, sk-def-pic, lem-sc-divisor-class-curve;
Stacks Project, Divisors, Tags 0BE9 and 0BE8 (blueprint: lem-sc-divisor-class-curve).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Divisor classes identify with the Picard group by sending a divisor to the class of its
associated module of rational functions with the specified valuation bounds.
Source: blueprint, sec-curve-estimates, sk-def-pic, lem-sc-divisor-class-curve;
Stacks Project, Divisors, Tags 0BE9 and 0BE8 (blueprint: lem-sc-divisor-class-curve).

Proof:
1. By `lem-sc-smooth-connected-curve-local-rings` the curve is integral and Noetherian, and
   its closed stalks are DVRs. Principal divisors form a subgroup by additivity of valuations
   (`def-sc-divisor`). The divisor module is invertible by `lem-sc-divisor-module-local`.
2. Multiplication by f inverse identifies O(D) with O(D + div(f)), on sections and compatibly
   with restrictions. In particular O(div(f)) is trivial, so the map factors through Cl(C).
3. Multiplication gives O(D) tensor O(D') isomorphic to O(D + D'). On neighbourhoods provided
   by `lem-sc-divisor-module-local` both sides have generator t to the power minus the sum of
   the coefficients. Thus the map respects the tensor group law of `lem-sc-pic-group`.
4. Every invertible module has a nonzero rational section s, and is O(div(s)), by
   `lem-sc-line-bundle-rational-section`. Therefore the map is surjective.
5. If O(D) is trivial, the image f of 1 under a trivialization generates its sections and
   stalks. At each closed point its valuation is minus the coefficient of D, by
   `lem-sc-divisor-module-local`. Hence D = div(f inverse), so the map is injective.
6. The well-defined bijective homomorphism is the required additive equivalence. Its image
   at each divisor is represented by precisely the module from `def-sc-divisor`.

No properness is required. The integral and Noetherian instances in the domain below are
consequences of the hypotheses, rather than additional assumptions. The representative
isomorphism expresses equality of Picard classes without choosing an invertibility proof. -/
theorem exists_divisorClassGroup_addEquiv_pic_associatedModule
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] :
    ∃ e : (@DivisorClassGroup C (C.smooth_connected_curve_local_rings k f).choose
        (isNoetherian_of_locallyOfFiniteType f)) ≃+ Additive C.Pic,
      ∀ D : C.Divisor,
        Nonempty ((fromSkeleton C.Modules).obj (e (QuotientAddGroup.mk D)).toMul.val ≅
          D.moduleOfSmoothConnectedCurve k C f) := by
  sorry

end AlgebraicGeometry.Scheme
